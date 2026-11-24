import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3706_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK PEqualNP.ReadTwo
  PEqualNP.SplitCount

/-! ### Generic `foldl` append helpers -/

private lemma foldl_append_length {α β : Type*} (f : List α → β → α) :
    ∀ (xs : List β) (init : List α),
      (xs.foldl (fun acc x => acc ++ [f acc x]) init).length = init.length + xs.length := by
  intro xs
  induction xs with
  | nil => intro init; simp
  | cons x rest ih =>
    intro init
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (init ++ [f init x])]
    simp; omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List α → β → α) (d : α) :
    ∀ (xs : List β) (init : List α) (i : ℕ), i < init.length →
      (xs.foldl (fun acc x => acc ++ [f acc x]) init).getD i d = init.getD i d := by
  intro xs
  induction xs with
  | nil => intro init i _; rfl
  | cons x rest ih =>
    intro init i hi
    simp only [List.foldl_cons]
    have hi' : i < (init ++ [f init x]).length := by simp; omega
    rw [ih (init ++ [f init x]) i hi']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma foldl_append_at {α β : Type*} (f : List α → β → α) (d : α)
    (xs : List β) (init : List α) (j : ℕ) (hj : j < xs.length) :
    (xs.foldl (fun acc x => acc ++ [f acc x]) init).getD (init.length + j) d =
      f ((xs.take j).foldl (fun acc x => acc ++ [f acc x]) init) (xs[j]'hj) := by
  have hsplit : xs = xs.take j ++ (xs[j]'hj) :: xs.drop (j + 1) := by
    have h1 := (List.take_append_drop j xs).symm
    have h2 : xs.drop j = (xs[j]'hj) :: xs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pref := (xs.take j).foldl (fun acc x => acc ++ [f acc x]) init
  have hplen : pref.length = init.length + j := by
    dsimp only [pref]
    rw [foldl_append_length, List.length_take]
    omega
  have hlt : init.length + j < (pref ++ [f pref (xs[j]'hj)]).length := by
    simp [hplen]
  rw [foldl_append_getD_lt f d (xs.drop (j + 1)) (pref ++ [f pref (xs[j]'hj)]) (init.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hplen, List.getElem?_append_right (le_refl _)]
  simp

private lemma foldl_append_prefix_getD {α β : Type*} (f : List α → β → α) (d : α)
    (xs : List β) (init : List α) (j : ℕ) (hj : j ≤ xs.length) (i : ℕ) (hi : i < init.length + j) :
    ((xs.take j).foldl (fun acc x => acc ++ [f acc x]) init).getD i d =
      (xs.foldl (fun acc x => acc ++ [f acc x]) init).getD i d := by
  set pref := (xs.take j).foldl (fun acc x => acc ++ [f acc x]) init
  have hplen : pref.length = init.length + j := by
    dsimp only [pref]
    rw [foldl_append_length, List.length_take]
    omega
  have hsplit : xs = xs.take j ++ xs.drop j := (List.take_append_drop j xs).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hi' : i < pref.length := by omega
  exact (foldl_append_getD_lt f d (xs.drop j) pref i hi').symm

/-! ### Basic `IsAO2`, `wval`, and `graphFun` lemmas -/

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j]'hj := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

private lemma gate_mem_of_lt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq_getElem C j hj]
  exact List.getElem_mem hj

private lemma ao2_gate_spec {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem := gate_mem_of_lt C j hj
  have hop := hAO2.1 (gateAt C j) hmem
  have hlen := hAO2.2.2 (gateAt C j) hmem
  have hrb := hAO2.2.1 j hj
  cases hinp : (gateAt C j).inputs with
  | nil => rw [hinp] at hlen; simp at hlen
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen; simp at hlen
    | cons b rest2 =>
      cases rest2 with
      | cons c rest3 => rw [hinp] at hlen; simp at hlen
      | nil =>
        have h0 : opnd C j 0 = a := by unfold opnd; rw [hinp]; rfl
        have h1 : opnd C j 1 = b := by unfold opnd; rw [hinp]; rfl
        have ha : a < n + j := hrb a (by rw [hinp]; simp)
        have hb : b < n + j := hrb b (by rw [hinp]; simp)
        exact ⟨hop, by rw [h0, h1], h0 ▸ ha, h1 ▸ hb⟩

private lemma wires_length {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length]
  simp

private lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by rw [wires_length]; exact hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
  rfl

private lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := by simp
  have hi' : i < (List.ofFn x).length := by omega
  rw [foldl_append_getD_lt _ false C.gates (List.ofFn x) i hi']
  rw [List.getD_eq_getElem?_getD]
  simp only [List.getElem?_ofFn, hi, dite_true, Option.getD_some]

private lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

private lemma gateVal_eval {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wval C x w) := by
  unfold gateVal Circuit.wires
  have hlen : (List.ofFn x).length = n := by simp
  have hat := foldl_append_at (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) false C.gates (List.ofFn x) j hj
  rw [hlen] at hat
  rw [hat, ← gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hrb : w < n + j := hAO2.2.1 j hj w hw
  have hpref := foldl_append_prefix_getD
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) false
    C.gates (List.ofFn x) j (Nat.le_of_lt hj) w (by rw [hlen]; exact hrb)
  exact hpref

private lemma gateVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C j x = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  obtain ⟨_, hinp, _, _⟩ := ao2_gate_spec hAO2 j hj
  rw [gateVal_eval hAO2 j hj x, hor, hinp]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]

private lemma gateVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  obtain ⟨_, hinp, _, _⟩ := ao2_gate_spec hAO2 j hj
  rw [gateVal_eval hAO2 j hj x, hand, hinp]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]

private lemma wval_mono {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, w < n + C.gates.length → wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwx
    by_cases hlt : w < n
    · rw [wval_input C x w hlt] at hwx
      rw [wval_input C y w hlt]
      exact hxy ⟨w, hlt⟩ hwx
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq, ← gateVal_eq_wval] at hwx ⊢
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [gateVal_and hAO2 (w - n) hj hand] at hwx ⊢
        rw [Bool.and_eq_true] at hwx ⊢
        exact ⟨ih _ (by omega) (by omega) hwx.1, ih _ (by omega) (by omega) hwx.2⟩
      · rw [gateVal_or hAO2 (w - n) hj hor] at hwx ⊢
        rw [Bool.or_eq_true] at hwx ⊢
        rcases hwx with h | h
        · exact Or.inl (ih _ (by omega) (by omega) h)
        · exact Or.inr (ih _ (by omega) (by omega) h)

private lemma graphFun_empty_unit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (unitInput u) = false := by
  unfold graphFun unitInput
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  have ha' : a = u := of_decide_eq_true ha
  have hb' : b = u := of_decide_eq_true hb
  subst ha' hb'
  exact G.ne_of_adj hab rfl

private lemma graphFun_empty_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  unfold graphFun pairInput
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl (G.ne_of_adj hab)
    · exact hab
    · exact hab.symm
    · exact absurd rfl (G.ne_of_adj hab)
  · intro huv
    exact ⟨u, v, huv, by simp, by simp⟩

private lemma input_not_belowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) (hw : w < n) :
    ¬ (∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) := by
  intro h
  let u : Fin n := ⟨w, hw⟩
  have h1 : wval C (unitInput u) w = true := by
    rw [wval_input C _ w hw]
    simp [unitInput, u]
  have h2 := h (unitInput u) h1
  rw [graphFun_empty_unit G u] at h2
  exact Bool.noConfusion h2

private lemma or_belowF_operands {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO2 : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (hbj : BelowF G C j) :
    ∀ b : Fin 2, n ≤ opnd C j b ∧ opnd C j b < n + j ∧ BelowF G C (opnd C j b - n) := by
  obtain ⟨_, _, h0, h1⟩ := ao2_gate_spec hAO2 j hj
  intro b
  have hlt : opnd C j b < n + j := by fin_cases b <;> assumption
  have hsub : ∀ x : Fin n → Bool, wval C x (opnd C j b) = true → graphFun G ∅ x = true := by
    intro x hwx
    apply hbj x
    rw [gateVal_or hAO2 j hj hor x, Bool.or_eq_true]
    fin_cases b
    · exact Or.inl hwx
    · exact Or.inr hwx
  have hge : n ≤ opnd C j b := by
    by_contra hlt_n
    push Not at hlt_n
    exact input_not_belowF G C (opnd C j b) hlt_n hsub
  refine ⟨hge, hlt, ?_⟩
  intro x hx
  apply hsub x
  have heq : n + (opnd C j b - n) = opnd C j b := by omega
  rw [← heq]
  exact hx

/-! ### `Vset`, `Gset`, and `orCone` via `foldl` -/

private def vsetStep {n : ℕ} (acc : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  match g.op with
  | GateOp.or => acc.getD (g.inputs.getD 0 0) ∅ ∪ acc.getD (g.inputs.getD 1 0) ∅
  | _ => ∅

private def vsetList (n : ℕ) (C : Circuit) : List (Finset (Fin n)) :=
  C.gates.foldl (fun acc g => acc ++ [vsetStep acc g]) ((List.finRange n).map fun i => {i})

private def Vset (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  (vsetList n C).getD w ∅

private lemma vset_input (n : ℕ) (C : Circuit) (i : ℕ) (hi : i < n) :
    Vset n C i = {⟨i, hi⟩} := by
  unfold Vset vsetList
  have hlen : ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n))).length = n := by simp
  rw [foldl_append_getD_lt vsetStep ∅ C.gates _ i (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

private lemma vset_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    Vset n C (n + j) = match (gateAt C j).op with
      | GateOp.or => Vset n C (opnd C j 0) ∪ Vset n C (opnd C j 1)
      | _ => ∅ := by
  unfold Vset vsetList
  have hlen : ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n))).length = n := by simp
  have hat := foldl_append_at vsetStep ∅ C.gates ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n))) j hj
  rw [hlen] at hat
  rw [hat, ← gateAt_eq_getElem C j hj]
  set pref := (C.gates.take j).foldl (fun acc g => acc ++ [vsetStep acc g]) ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n)))
  obtain ⟨_, _, h0, h1⟩ := ao2_gate_spec hAO2 j hj
  have hp0 : pref.getD (opnd C j 0) ∅ = (C.gates.foldl (fun acc g => acc ++ [vsetStep acc g]) ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n)))).getD (opnd C j 0) ∅ :=
    foldl_append_prefix_getD vsetStep ∅ C.gates ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n))) j (Nat.le_of_lt hj) (opnd C j 0) (by rw [hlen]; exact h0)
  have hp1 : pref.getD (opnd C j 1) ∅ = (C.gates.foldl (fun acc g => acc ++ [vsetStep acc g]) ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n)))).getD (opnd C j 1) ∅ :=
    foldl_append_prefix_getD vsetStep ∅ C.gates ((List.finRange n).map fun k : Fin n => ({k} : Finset (Fin n))) j (Nat.le_of_lt hj) (opnd C j 1) (by rw [hlen]; exact h1)
  unfold vsetStep
  cases (gateAt C j).op
  · rfl
  · simp only [opnd, Fin.val_zero, Fin.val_one] at hp0 hp1 ⊢
    rw [hp0, hp1]; rfl
  · rfl
  · rfl
  · rfl

private lemma vset_wval_unit {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ w : ℕ, w < n + C.gates.length → ∀ x ∈ Vset n C w, wval C (unitInput x) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hlt : w < n
    · rw [vset_input n C w hlt, Finset.mem_singleton] at hx
      rw [wval_input C _ w hlt, hx]
      simp [unitInput]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hx ⊢
      rw [vset_gate hAO2 (w - n) hj] at hx
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [hand] at hx; simp at hx
      · rw [hor] at hx
        rw [← gateVal_eq_wval, gateVal_or hAO2 (w - n) hj hor, Bool.or_eq_true]
        rcases Finset.mem_union.mp hx with hx0 | hx1
        · exact Or.inl (ih _ (by omega) (by omega) x hx0)
        · exact Or.inr (ih _ (by omega) (by omega) x hx1)

private def gsetStep (n : ℕ) (acc : List (Finset ℕ)) (g : Gate) : Finset ℕ :=
  match g.op with
  | GateOp.or => insert (acc.length - n) (acc.getD (g.inputs.getD 0 0) ∅ ∪ acc.getD (g.inputs.getD 1 0) ∅)
  | _ => ∅

private def gsetList (n : ℕ) (C : Circuit) : List (Finset ℕ) :=
  C.gates.foldl (fun acc g => acc ++ [gsetStep n acc g]) (List.replicate n ∅)

private def Gset (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  (gsetList n C).getD w ∅

private lemma gset_input (n : ℕ) (C : Circuit) (i : ℕ) (hi : i < n) :
    Gset n C i = ∅ := by
  unfold Gset gsetList
  have hlen : (List.replicate n (∅ : Finset ℕ)).length = n := by simp
  rw [foldl_append_getD_lt (gsetStep n) ∅ C.gates _ i (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

private lemma gset_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    Gset n C (n + j) = match (gateAt C j).op with
      | GateOp.or => insert j (Gset n C (opnd C j 0) ∪ Gset n C (opnd C j 1))
      | _ => ∅ := by
  unfold Gset gsetList
  have hlen : (List.replicate n (∅ : Finset ℕ)).length = n := by simp
  have hat := foldl_append_at (gsetStep n) ∅ C.gates (List.replicate n ∅) j hj
  rw [hlen] at hat
  rw [hat, ← gateAt_eq_getElem C j hj]
  set pref := (C.gates.take j).foldl (fun acc g => acc ++ [gsetStep n acc g]) (List.replicate n ∅)
  have hplen : pref.length = n + j := by
    dsimp only [pref]
    rw [foldl_append_length, hlen, List.length_take]; omega
  obtain ⟨_, _, h0, h1⟩ := ao2_gate_spec hAO2 j hj
  have hp0 : pref.getD (opnd C j 0) ∅ = (C.gates.foldl (fun acc g => acc ++ [gsetStep n acc g]) (List.replicate n ∅)).getD (opnd C j 0) ∅ :=
    foldl_append_prefix_getD (gsetStep n) ∅ C.gates (List.replicate n ∅) j (Nat.le_of_lt hj) (opnd C j 0) (by rw [hlen]; exact h0)
  have hp1 : pref.getD (opnd C j 1) ∅ = (C.gates.foldl (fun acc g => acc ++ [gsetStep n acc g]) (List.replicate n ∅)).getD (opnd C j 1) ∅ :=
    foldl_append_prefix_getD (gsetStep n) ∅ C.gates (List.replicate n ∅) j (Nat.le_of_lt hj) (opnd C j 1) (by rw [hlen]; exact h1)
  unfold gsetStep
  cases (gateAt C j).op
  · rfl
  · simp only [opnd, Fin.val_zero, Fin.val_one] at hp0 hp1 ⊢
    rw [hplen, Nat.add_sub_cancel_left, hp0, hp1]; rfl
  · rfl
  · rfl
  · rfl

private lemma gset_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ w : ℕ, w < n + C.gates.length → ∀ h ∈ Gset n C w,
      h < C.gates.length ∧ n + h ≤ w ∧ (gateAt C h).op = GateOp.or ∧ Vset n C (n + h) ⊆ Vset n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw h hh
    by_cases hlt : w < n
    · rw [gset_input n C w hlt] at hh; simp at hh
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hh ⊢
      rw [gset_gate hAO2 (w - n) hj] at hh
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [hand] at hh; simp at hh
      · rw [hor] at hh
        rw [vset_gate hAO2 (w - n) hj, hor]
        rcases Finset.mem_insert.mp hh with rfl | hmem
        · refine ⟨hj, le_refl _, hor, ?_⟩
          rw [vset_gate hAO2 (w - n) hj, hor]
        · rcases Finset.mem_union.mp hmem with hmem0 | hmem1
          · obtain ⟨hlt', hle', hop', hsub'⟩ := ih _ (by omega) (by omega) h hmem0
            exact ⟨hlt', by omega, hop', hsub'.trans Finset.subset_union_left⟩
          · obtain ⟨hlt', hle', hop', hsub'⟩ := ih _ (by omega) (by omega) h hmem1
            exact ⟨hlt', by omega, hop', hsub'.trans Finset.subset_union_right⟩

private def orConeStep (n : ℕ) (acc : List (Finset ℕ)) (g : Gate) : Finset ℕ :=
  match g.op with
  | GateOp.or =>
    let w0 := g.inputs.getD 0 0
    let w1 := g.inputs.getD 1 0
    let s0 := if n ≤ w0 ∧ w0 < n + acc.length then acc.getD (w0 - n) ∅ else ∅
    let s1 := if n ≤ w1 ∧ w1 < n + acc.length then acc.getD (w1 - n) ∅ else ∅
    insert acc.length (s0 ∪ s1)
  | _ => {acc.length}

private def orConeList (n : ℕ) (C : Circuit) : List (Finset ℕ) :=
  C.gates.foldl (fun acc g => acc ++ [orConeStep n acc g]) []

private def orCone (n : ℕ) (C : Circuit) (j : ℕ) : Finset ℕ :=
  (orConeList n C).getD j ∅

private lemma orCone_at {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    orCone n C j = match (gateAt C j).op with
      | GateOp.or =>
        let w0 := opnd C j 0
        let w1 := opnd C j 1
        let s0 := if n ≤ w0 ∧ w0 < n + j then orCone n C (w0 - n) else ∅
        let s1 := if n ≤ w1 ∧ w1 < n + j then orCone n C (w1 - n) else ∅
        insert j (s0 ∪ s1)
      | _ => {j} := by
  unfold orCone orConeList
  have hlen : ([] : List (Finset ℕ)).length = 0 := rfl
  have hat := foldl_append_at (orConeStep n) ∅ C.gates [] j hj
  simp only [hlen, Nat.zero_add] at hat
  rw [hat, ← gateAt_eq_getElem C j hj]
  set pref := (C.gates.take j).foldl (fun acc g => acc ++ [orConeStep n acc g]) []
  have hplen : pref.length = j := by
    dsimp only [pref]
    rw [foldl_append_length, hlen, Nat.zero_add, List.length_take]; omega
  have hcongr : ∀ w : ℕ,
      (if n ≤ w ∧ w < n + j then pref.getD (w - n) ∅ else ∅) =
      (if n ≤ w ∧ w < n + j then
        (C.gates.foldl (fun acc g => acc ++ [orConeStep n acc g]) []).getD (w - n) ∅
      else ∅) := by
    intro w
    split_ifs with hw
    · exact foldl_append_prefix_getD (orConeStep n) ∅ C.gates [] j (Nat.le_of_lt hj) (w - n) (by simp; omega)
    · rfl
  unfold orConeStep
  cases (gateAt C j).op
  · dsimp only; rw [hplen]
  · dsimp only [opnd]
    simp only [Fin.val_zero, Fin.val_one]
    rw [hplen, hcongr ((gateAt C j).inputs.getD 0 0), hcongr ((gateAt C j).inputs.getD 1 0)]; rfl
  · dsimp only; rw [hplen]
  · dsimp only; rw [hplen]
  · dsimp only; rw [hplen]

private lemma mem_orCone_self {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    j ∈ orCone n C j := by
  rw [orCone_at C j hj]
  cases (gateAt C j).op <;> simp

private lemma orCone_belowF_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (hbj : BelowF G C j) :
    orCone n C j = insert j (orCone n C (opnd C j 0 - n) ∪ orCone n C (opnd C j 1 - n)) := by
  have h0 := or_belowF_operands G C hAO2 j hj hor hbj 0
  have h1 := or_belowF_operands G C hAO2 j hj hor hbj 1
  rw [orCone_at C j hj, hor]
  simp only [h0.1, h0.2.1, h1.1, h1.2.1, and_self, ite_true]

private lemma orCone_props {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ j : ℕ, j < C.gates.length → BelowF G C j →
      ∀ m ∈ orCone n C j,
        m ≤ j ∧ BelowF G C m ∧
        (m ≠ j → ∃ k ∈ orCone n C j, (gateAt C k).op = GateOp.or ∧
          (m = opnd C k 0 - n ∨ m = opnd C k 1 - n)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hbj m hm
    obtain ⟨hop, _, _, _⟩ := ao2_gate_spec hAO2 j hj
    rcases hop with hand | hor
    · rw [orCone_at C j hj, hand, Finset.mem_singleton] at hm
      subst hm
      exact ⟨le_refl _, hbj, fun h => absurd rfl h⟩
    · have h0 := or_belowF_operands G C hAO2 j hj hor hbj 0
      have h1 := or_belowF_operands G C hAO2 j hj hor hbj 1
      have hoc := orCone_belowF_or G hAO2 j hj hor hbj
      rw [hoc] at hm
      rcases Finset.mem_insert.mp hm with rfl | hmem
      · exact ⟨le_refl _, hbj, fun h => absurd rfl h⟩
      · rcases Finset.mem_union.mp hmem with hm0 | hm1
        · obtain ⟨hle, hbm, hpar⟩ := ih (opnd C j 0 - n) (by omega) (by omega) h0.2.2 m hm0
          refine ⟨by omega, hbm, fun _ => ?_⟩
          by_cases heq : m = opnd C j 0 - n
          · exact ⟨j, mem_orCone_self C j hj, hor, Or.inl heq⟩
          · obtain ⟨k, hk, hkor, hkpar⟩ := hpar heq
            exact ⟨k, by rw [hoc]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hk), hkor, hkpar⟩
        · obtain ⟨hle, hbm, hpar⟩ := ih (opnd C j 1 - n) (by omega) (by omega) h1.2.2 m hm1
          refine ⟨by omega, hbm, fun _ => ?_⟩
          by_cases heq : m = opnd C j 1 - n
          · exact ⟨j, mem_orCone_self C j hj, hor, Or.inr heq⟩
          · obtain ⟨k, hk, hkor, hkpar⟩ := hpar heq
            exact ⟨k, by rw [hoc]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hk), hkor, hkpar⟩

/-! ### `readVectors` soundness for `S = [u.val, v.val]`, `k = 1` -/

private lemma mem_insertNew_iff (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (hx | rfl); exact hx; exact h
  · simp

private lemma mem_foldl_insertNew_iff :
    ∀ (A acc : List (List ℕ)) (x : List ℕ),
      x ∈ A.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ A := by
  intro A
  induction A with
  | nil => intro acc x; simp
  | cons a rest ih =>
    intro acc x
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih (insertNew acc a) x, mem_insertNew_iff]
    tauto

private lemma mem_andStep_iff (k : ℕ) (A B : List (List ℕ)) (x : List ℕ) :
    x ∈ andStep k A B ↔ ∃ a ∈ A, ∃ b ∈ B, x = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew_iff]
  simp [List.mem_flatMap, List.mem_map, eq_comm]

private lemma readVectors_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (i : ℕ) (hi : i < n) :
    (readVectors C n S k).getD i [] = leafVectors S k i := by
  unfold readVectors
  have hlen : ((List.range n).map (leafVectors S k)).length = n := by simp
  rw [foldl_append_getD_lt _ [] C.gates _ i (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

private def rvStep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

private lemma readVectors_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let A := (readVectors C n S k).getD (opnd C j 0) []
      let B := (readVectors C n S k).getD (opnd C j 1) []
      match (gateAt C j).op with
      | GateOp.or => B.foldl insertNew (A.foldl insertNew [])
      | GateOp.and => andStep k (andStep k [S.map fun _ => 0] A) B
      | _ => [] := by
  have hrv_def : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [rvStep S k R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv_def]
  have hlen : ((List.range n).map (leafVectors S k)).length = n := by simp
  have hat := foldl_append_at (rvStep S k) [] C.gates ((List.range n).map (leafVectors S k)) j hj
  rw [hlen] at hat
  rw [hat, ← gateAt_eq_getElem C j hj]
  set pref := (C.gates.take j).foldl (fun R g => R ++ [rvStep S k R g]) ((List.range n).map (leafVectors S k))
  obtain ⟨_, hinp, h0, h1⟩ := ao2_gate_spec hAO2 j hj
  have hp0 : pref.getD (opnd C j 0) [] = (C.gates.foldl (fun R g => R ++ [rvStep S k R g]) ((List.range n).map (leafVectors S k))).getD (opnd C j 0) [] :=
    foldl_append_prefix_getD (rvStep S k) [] C.gates ((List.range n).map (leafVectors S k)) j (Nat.le_of_lt hj) (opnd C j 0) (by rw [hlen]; exact h0)
  have hp1 : pref.getD (opnd C j 1) [] = (C.gates.foldl (fun R g => R ++ [rvStep S k R g]) ((List.range n).map (leafVectors S k))).getD (opnd C j 1) [] :=
    foldl_append_prefix_getD (rvStep S k) [] C.gates ((List.range n).map (leafVectors S k)) j (Nat.le_of_lt hj) (opnd C j 1) (by rw [hlen]; exact h1)
  unfold rvStep
  rw [hinp]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  cases (gateAt C j).op
  · dsimp only; rw [hp0, hp1]; rfl
  · dsimp only; rw [hp0, hp1]; rfl
  · rfl
  · rfl
  · rfl

private lemma capAdd_pair (a0 a1 b0 b1 : ℕ) :
    capAdd 1 [a0, a1] [b0, b1] = [min (a0 + b0) 2, min (a1 + b1) 2] := rfl

private lemma rv_pair_shape {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w : ℕ, w < n + C.gates.length →
      ∀ vec ∈ (readVectors C n [u.val, v.val] 1).getD w [],
        ∃ a b : ℕ, vec = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw vec hvec
    by_cases hlt : w < n
    · rw [readVectors_input C n [u.val, v.val] 1 w hlt] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem hvec
        subst hvec
        rcases hmem with rfl | rfl
        · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
          refine ⟨1, 0, ?_, by omega, by omega, by omega⟩
          simp [hne]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          refine ⟨0, 1, ?_, by omega, by omega, by omega⟩
          simp [hne]
      · simp at hvec
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hvec
      rw [readVectors_gate hAO2 [u.val, v.val] 1 (w - n) hj] at hvec
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [hand] at hvec
        dsimp only at hvec
        rw [mem_andStep_iff] at hvec
        obtain ⟨x, hx, q, hq, rfl⟩ := hvec
        rw [mem_andStep_iff] at hx
        obtain ⟨z, hz, p, hp, rfl⟩ := hx
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        subst hz
        obtain ⟨p0, p1, rfl, hp0, hp1, hpsum⟩ := ih _ (by omega) (by omega) p hp
        obtain ⟨q0, q1, rfl, hq0, hq1, hqsum⟩ := ih _ (by omega) (by omega) q hq
        rw [capAdd_pair, capAdd_pair]
        exact ⟨min (min (0 + p0) 2 + q0) 2, min (min (0 + p1) 2 + q1) 2, rfl, by omega, by omega, by omega⟩
      · rw [hor] at hvec
        dsimp only at hvec
        rw [mem_foldl_insertNew_iff, mem_foldl_insertNew_iff] at hvec
        rcases hvec with (h_nil | hp) | hq
        · simp at h_nil
        · exact ih _ (by omega) (by omega) vec hp
        · exact ih _ (by omega) (by omega) vec hq

private lemma rv_and_mem_iff {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (vec : List ℕ) :
    vec ∈ (readVectors C n [u.val, v.val] 1).getD (n + j) [] ↔
      ∃ p0 p1 q0 q1 : ℕ,
        [p0, p1] ∈ (readVectors C n [u.val, v.val] 1).getD (opnd C j 0) [] ∧
        [q0, q1] ∈ (readVectors C n [u.val, v.val] 1).getD (opnd C j 1) [] ∧
        vec = [min (p0 + q0) 2, min (p1 + q1) 2] := by
  obtain ⟨_, _, h0, h1⟩ := ao2_gate_spec hAO2 j hj
  rw [readVectors_gate hAO2 [u.val, v.val] 1 j hj, hand]
  dsimp only
  constructor
  · intro hvec
    rw [mem_andStep_iff] at hvec
    obtain ⟨x, hx, q, hq, rfl⟩ := hvec
    rw [mem_andStep_iff] at hx
    obtain ⟨z, hz, p, hp, rfl⟩ := hx
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    subst hz
    obtain ⟨p0, p1, rfl, hp0, hp1, _⟩ := rv_pair_shape hAO2 u v huv _ (by omega) p hp
    obtain ⟨q0, q1, rfl, hq0, hq1, _⟩ := rv_pair_shape hAO2 u v huv _ (by omega) q hq
    refine ⟨p0, p1, q0, q1, hp, hq, ?_⟩
    rw [capAdd_pair, capAdd_pair]
    simp only [Nat.zero_add, Nat.min_eq_left hp0, Nat.min_eq_left hp1]
  · rintro ⟨p0, p1, q0, q1, hp, hq, rfl⟩
    obtain ⟨p0', p1', hpeq, hp0, hp1, _⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [p0, p1] hp
    simp only [List.cons.injEq, and_true] at hpeq
    obtain ⟨rfl, rfl⟩ := hpeq
    rw [mem_andStep_iff]
    refine ⟨capAdd 1 [0, 0] [p0, p1], ?_, [q0, q1], hq, ?_⟩
    · rw [mem_andStep_iff]
      exact ⟨[0, 0], by simp, [p0, p1], hp, rfl⟩
    · rw [capAdd_pair, capAdd_pair]
      simp only [Nat.zero_add, Nat.min_eq_left hp0, Nat.min_eq_left hp1]

private lemma rv_or_mem_iff {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (vec : List ℕ) :
    vec ∈ (readVectors C n [u.val, v.val] 1).getD (n + j) [] ↔
      vec ∈ (readVectors C n [u.val, v.val] 1).getD (opnd C j 0) [] ∨
      vec ∈ (readVectors C n [u.val, v.val] 1).getD (opnd C j 1) [] := by
  rw [readVectors_gate hAO2 [u.val, v.val] 1 j hj, hor]
  dsimp only
  rw [mem_foldl_insertNew_iff, mem_foldl_insertNew_iff]
  simp

private lemma rv_zero_snd_wval {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w : ℕ, w < n + C.gates.length →
      ∀ a : ℕ, [a, 0] ∈ (readVectors C n [u.val, v.val] 1).getD w [] →
        wval C (unitInput u) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw a hvec
    by_cases hlt : w < n
    · rw [readVectors_input C n [u.val, v.val] 1 w hlt] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem hvec
        rcases hmem with rfl | rfl
        · rw [wval_input C _ u.val u.isLt]; simp [unitInput]
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          simp [hne] at hvec
      · simp at hvec
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hvec ⊢
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [rv_and_mem_iff hAO2 u v huv (w - n) hj hand] at hvec
        obtain ⟨p0, p1, q0, q1, hp, hq, heq⟩ := hvec
        simp only [List.cons.injEq, and_true] at heq
        have hp1 : p1 = 0 := by omega
        have hq1 : q1 = 0 := by omega
        subst hp1 hq1
        rw [← gateVal_eq_wval, gateVal_and hAO2 (w - n) hj hand, Bool.and_eq_true]
        exact ⟨ih _ (by omega) (by omega) p0 hp, ih _ (by omega) (by omega) q0 hq⟩
      · rw [rv_or_mem_iff hAO2 u v (w - n) hj hor] at hvec
        rw [← gateVal_eq_wval, gateVal_or hAO2 (w - n) hj hor, Bool.or_eq_true]
        rcases hvec with hp | hq
        · exact Or.inl (ih _ (by omega) (by omega) a hp)
        · exact Or.inr (ih _ (by omega) (by omega) a hq)

private lemma rv_zero_fst_wval {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w : ℕ, w < n + C.gates.length →
      ∀ b : ℕ, [0, b] ∈ (readVectors C n [u.val, v.val] 1).getD w [] →
        wval C (unitInput v) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw b hvec
    by_cases hlt : w < n
    · rw [readVectors_input C n [u.val, v.val] 1 w hlt] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem hvec
        rcases hmem with rfl | rfl
        · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
          simp [hne] at hvec
        · rw [wval_input C _ v.val v.isLt]; simp [unitInput]
      · simp at hvec
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hvec ⊢
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [rv_and_mem_iff hAO2 u v huv (w - n) hj hand] at hvec
        obtain ⟨p0, p1, q0, q1, hp, hq, heq⟩ := hvec
        simp only [List.cons.injEq, and_true] at heq
        have hp0 : p0 = 0 := by omega
        have hq0 : q0 = 0 := by omega
        subst hp0 hq0
        rw [← gateVal_eq_wval, gateVal_and hAO2 (w - n) hj hand, Bool.and_eq_true]
        exact ⟨ih _ (by omega) (by omega) p1 hp, ih _ (by omega) (by omega) q1 hq⟩
      · rw [rv_or_mem_iff hAO2 u v (w - n) hj hor] at hvec
        rw [← gateVal_eq_wval, gateVal_or hAO2 (w - n) hj hor, Bool.or_eq_true]
        rcases hvec with hp | hq
        · exact Or.inl (ih _ (by omega) (by omega) b hp)
        · exact Or.inr (ih _ (by omega) (by omega) b hq)

private lemma rv_unit_fst_vset {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w : ℕ, w < n + C.gates.length →
      [1, 0] ∈ (readVectors C n [u.val, v.val] 1).getD w [] → u ∈ Vset n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hvec
    by_cases hlt : w < n
    · rw [readVectors_input C n [u.val, v.val] 1 w hlt] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem hvec
        rcases hmem with rfl | rfl
        · rw [vset_input n C u.val u.isLt]; simp
        · have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
          simp [hne] at hvec
      · simp at hvec
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hvec ⊢
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [rv_and_mem_iff hAO2 u v huv (w - n) hj hand] at hvec
        obtain ⟨p0, p1, q0, q1, hp, hq, heq⟩ := hvec
        obtain ⟨p0', p1', hpeq, _, _, hpsum⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [p0, p1] hp
        obtain ⟨q0', q1', hqeq, _, _, hqsum⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [q0, q1] hq
        simp only [List.cons.injEq, and_true] at heq hpeq hqeq
        omega
      · rw [rv_or_mem_iff hAO2 u v (w - n) hj hor] at hvec
        rw [vset_gate hAO2 (w - n) hj, hor, Finset.mem_union]
        rcases hvec with hp | hq
        · exact Or.inl (ih _ (by omega) (by omega) hp)
        · exact Or.inr (ih _ (by omega) (by omega) hq)

private lemma rv_unit_snd_vset {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ w : ℕ, w < n + C.gates.length →
      [0, 1] ∈ (readVectors C n [u.val, v.val] 1).getD w [] → v ∈ Vset n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hvec
    by_cases hlt : w < n
    · rw [readVectors_input C n [u.val, v.val] 1 w hlt] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem hvec
        rcases hmem with rfl | rfl
        · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
          simp [hne] at hvec
        · rw [vset_input n C v.val v.isLt]; simp
      · simp at hvec
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn] at hvec ⊢
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 (w - n) hj
      rcases hop with hand | hor
      · rw [rv_and_mem_iff hAO2 u v huv (w - n) hj hand] at hvec
        obtain ⟨p0, p1, q0, q1, hp, hq, heq⟩ := hvec
        obtain ⟨p0', p1', hpeq, _, _, hpsum⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [p0, p1] hp
        obtain ⟨q0', q1', hqeq, _, _, hqsum⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [q0, q1] hq
        simp only [List.cons.injEq, and_true] at heq hpeq hqeq
        omega
      · rw [rv_or_mem_iff hAO2 u v (w - n) hj hor] at hvec
        rw [vset_gate hAO2 (w - n) hj, hor, Finset.mem_union]
        rcases hvec with hp | hq
        · exact Or.inl (ih _ (by omega) (by omega) hp)
        · exact Or.inr (ih _ (by omega) (by omega) hq)

private lemma descent_to_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO2 : IsAO2 n C) (u v : Fin n) (huv : u ≠ v) :
    ∀ j : ℕ, j < C.gates.length → BelowF G C j →
      [1, 1] ∈ (readVectors C n [u.val, v.val] 1).getD (n + j) [] →
      ∃ a ∈ orCone n C j, (gateAt C a).op = GateOp.and ∧
        ((u ∈ Vset n C (opnd C a 0) ∧ v ∈ Vset n C (opnd C a 1)) ∨
         (v ∈ Vset n C (opnd C a 0) ∧ u ∈ Vset n C (opnd C a 1))) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hbj h11
    obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 j hj
    rcases hop with hand | hor
    · refine ⟨j, mem_orCone_self C j hj, hand, ?_⟩
      rw [rv_and_mem_iff hAO2 u v huv j hj hand] at h11
      obtain ⟨p0, p1, q0, q1, hp, hq, heq⟩ := h11
      obtain ⟨p0', p1', hpeq, _, _, hpsum⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [p0, p1] hp
      obtain ⟨q0', q1', hqeq, _, _, hqsum⟩ := rv_pair_shape hAO2 u v huv _ (by omega) [q0, q1] hq
      simp only [List.cons.injEq, and_true] at heq hpeq hqeq
      have hcases : (p0 = 1 ∧ p1 = 0 ∧ q0 = 0 ∧ q1 = 1) ∨ (p0 = 0 ∧ p1 = 1 ∧ q0 = 1 ∧ q1 = 0) := by omega
      rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl ⟨rv_unit_fst_vset hAO2 u v huv _ (by omega) hp,
                      rv_unit_snd_vset hAO2 u v huv _ (by omega) hq⟩
      · exact Or.inr ⟨rv_unit_snd_vset hAO2 u v huv _ (by omega) hp,
                      rv_unit_fst_vset hAO2 u v huv _ (by omega) hq⟩
    · have hb0 := or_belowF_operands G C hAO2 j hj hor hbj 0
      have hb1 := or_belowF_operands G C hAO2 j hj hor hbj 1
      have hoc := orCone_belowF_or G hAO2 j hj hor hbj
      rw [rv_or_mem_iff hAO2 u v j hj hor] at h11
      rcases h11 with hp | hq
      · have heq0 : n + (opnd C j 0 - n) = opnd C j 0 := by omega
        rw [← heq0] at hp
        obtain ⟨a, ha, hand, hside⟩ := ih (opnd C j 0 - n) (by omega) (by omega) hb0.2.2 hp
        exact ⟨a, by rw [hoc]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ha), hand, hside⟩
      · have heq1 : n + (opnd C j 1 - n) = opnd C j 1 := by omega
        rw [← heq1] at hq
        obtain ⟨a, ha, hand, hside⟩ := ih (opnd C j 1 - n) (by omega) (by omega) hb1.2.2 hq
        exact ⟨a, by rw [hoc]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ha), hand, hside⟩

/-! ### Leaf OR frontier peeling bound -/

private def Reach (n : ℕ) (C : Circuit) (F : Finset ℕ) : Finset (Fin n) :=
  F.biUnion (Vset n C)

private def Big (n : ℕ) (C : Circuit) (F : Finset ℕ) : Finset ℕ :=
  (F.biUnion (Gset n C)).filter fun h => 2 ≤ (Vset n C (n + h)).card

private lemma or_cover_bound {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ m : ℕ, ∀ F : Finset ℕ,
      (Big n C F).card = m →
      (∀ w ∈ F, w < n + C.gates.length) →
      (Reach n C F).card ≤ F.card + m := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro F hm hFb
    let B := F.filter fun w => 2 ≤ (Vset n C w).card
    by_cases hB : B.Nonempty
    · let w_max := B.max' hB
      have hw_mem_B : w_max ∈ B := Finset.max'_mem B hB
      have hw_mem_F : w_max ∈ F := (Finset.mem_filter.mp hw_mem_B).1
      have hw_card : 2 ≤ (Vset n C w_max).card := (Finset.mem_filter.mp hw_mem_B).2
      have hw_lt : w_max < n + C.gates.length := hFb w_max hw_mem_F
      have hw_ge_n : n ≤ w_max := by
        by_contra hlt_n
        push Not at hlt_n
        rw [vset_input n C w_max hlt_n, Finset.card_singleton] at hw_card
        omega
      let h := w_max - n
      have hh_lt : h < C.gates.length := by omega
      have hwn : w_max = n + h := by omega
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_spec hAO2 h hh_lt
      have hhor : (gateAt C h).op = GateOp.or := by
        rcases hop with hand | hor
        · rw [hwn, vset_gate hAO2 h hh_lt, hand, Finset.card_empty] at hw_card
          omega
        · exact hor
      have hh_mem_Big : h ∈ Big n C F := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w_max, hw_mem_F, ?_⟩, ?_⟩
        · rw [hwn, gset_gate hAO2 h hh_lt, hhor]
          exact Finset.mem_insert_self _ _
        · rwa [← hwn]
      let F' : Finset ℕ := insert (opnd C h 0) (insert (opnd C h 1) (F.erase w_max))
      have hF'b : ∀ w ∈ F', w < n + C.gates.length := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw1
        · omega
        · rcases Finset.mem_insert.mp hw1 with rfl | hw2
          · omega
          · exact hFb w (Finset.mem_of_mem_erase hw2)
      have hReach : Reach n C F ⊆ Reach n C F' := by
        intro y hy
        obtain ⟨w, hwF, hyw⟩ := Finset.mem_biUnion.mp hy
        by_cases hww : w = w_max
        · subst hww
          rw [hwn, vset_gate hAO2 h hh_lt, hhor, Finset.mem_union] at hyw
          rcases hyw with hy0 | hy1
          · exact Finset.mem_biUnion.mpr ⟨opnd C h 0, Finset.mem_insert_self _ _, hy0⟩
          · exact Finset.mem_biUnion.mpr ⟨opnd C h 1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hy1⟩
        · exact Finset.mem_biUnion.mpr ⟨w,
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hww, hwF⟩)), hyw⟩
      have hBig_sub : Big n C F' ⊆ (Big n C F).erase h := by
        intro h' hh'
        obtain ⟨hmem_g, hcard'⟩ := Finset.mem_filter.mp hh'
        obtain ⟨w', hw'F', hh'g⟩ := Finset.mem_biUnion.mp hmem_g
        have hmem_BigF : h' ∈ Big n C F := by
          refine Finset.mem_filter.mpr ⟨?_, hcard'⟩
          rcases Finset.mem_insert.mp hw'F' with rfl | hw'1
          · refine Finset.mem_biUnion.mpr ⟨w_max, hw_mem_F, ?_⟩
            rw [hwn, gset_gate hAO2 h hh_lt, hhor]
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hh'g)
          · rcases Finset.mem_insert.mp hw'1 with rfl | hw'2
            · refine Finset.mem_biUnion.mpr ⟨w_max, hw_mem_F, ?_⟩
              rw [hwn, gset_gate hAO2 h hh_lt, hhor]
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hh'g)
            · exact Finset.mem_biUnion.mpr ⟨w', Finset.mem_of_mem_erase hw'2, hh'g⟩
        refine Finset.mem_erase.mpr ⟨?_, hmem_BigF⟩
        intro heq
        subst heq
        obtain ⟨_, hle_w', _, hsub_w'⟩ := gset_props hAO2 w' (hF'b w' hw'F') h hh'g
        have hcard_w' : 2 ≤ (Vset n C w').card := le_trans hcard' (Finset.card_le_card hsub_w')
        rcases Finset.mem_insert.mp hw'F' with rfl | hw'1
        · omega
        · rcases Finset.mem_insert.mp hw'1 with rfl | hw'2
          · omega
          · have hw'ne : w' ≠ w_max := (Finset.mem_erase.mp hw'2).1
            have hw'inB : w' ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hw'2, hcard_w'⟩
            have hw'le : w' ≤ w_max := Finset.le_max' B w' hw'inB
            omega
      have hBig_lt : (Big n C F').card < m := by
        have h1 : (Big n C F').card ≤ ((Big n C F).erase h).card := Finset.card_le_card hBig_sub
        have h2 : ((Big n C F).erase h).card = (Big n C F).card - 1 := Finset.card_erase_of_mem hh_mem_Big
        have h3 : 1 ≤ (Big n C F).card := Finset.one_le_card.mpr ⟨h, hh_mem_Big⟩
        omega
      have hF'_card : F'.card ≤ F.card + 1 := by
        have h1 : F'.card ≤ (insert (opnd C h 1) (F.erase w_max)).card + 1 := Finset.card_insert_le _ _
        have h2 : (insert (opnd C h 1) (F.erase w_max)).card ≤ (F.erase w_max).card + 1 := Finset.card_insert_le _ _
        have h3 : (F.erase w_max).card = F.card - 1 := Finset.card_erase_of_mem hw_mem_F
        have h4 : 1 ≤ F.card := Finset.one_le_card.mpr ⟨w_max, hw_mem_F⟩
        omega
      have hih := ih (Big n C F').card hBig_lt F' rfl hF'b
      have hrc := Finset.card_le_card hReach
      omega
    · have hall : ∀ w ∈ F, (Vset n C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        exact hB ⟨w, Finset.mem_filter.mpr ⟨hw, hgt⟩⟩
      calc (Reach n C F).card
          ≤ ∑ w ∈ F, (Vset n C w).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ F, 1 := Finset.sum_le_sum fun w hw => hall w hw
        _ = F.card := by simp
        _ ≤ F.card + m := Nat.le_add_right _ _

/-! ### Main D-ledger theorem -/

private lemma card_eq_one_eq_singleton_min {n : ℕ} (S : Finset (Fin n)) (h : S.card = 1) :
    S = {S.min' (Finset.card_pos.mp (by omega))} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : S.min' hne ∈ S := Finset.min'_mem S hne
  have heq : S.min' hne = c := Finset.mem_singleton.mp (hc ▸ hmem)
  rw [heq]
  exact hc

private lemma d_ledger_main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : Finset (Fin n))
    (hC4 : NoFourCycle G) (hAO2 : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hT : IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ReadTwiceAt n C (C.output - n) u v)) : Set (Sym2 (Fin n)))) T) :
    G.edgeFinset.card + T.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ReadTwiceAt n C (C.output - n) u v)).card + 1 := by
  letI := gateOpDecEq
  let D_edges : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ ReadTwiceAt n C (C.output - n) u v)
  let E1 : Finset (Sym2 (Fin n)) := G.edgeFinset \ D_edges
  let G1 : SimpleGraph (Fin n) := G.deleteEdges (D_edges : Set (Sym2 (Fin n)))
  have hD_sub : D_edges ⊆ G.edgeFinset := Finset.filter_subset _ _
  have hE_split : E1.card + D_edges.card = G.edgeFinset.card := Finset.card_sdiff_add_card_eq_card hD_sub
  suffices hgoal : E1.card + T.card ≤ C.size + 1 by
    change G.edgeFinset.card + T.card ≤ C.size + D_edges.card + 1
    omega
  by_cases hE1_empty : E1 = ∅
  · have hcov_empty : G1.IsVertexCover ((∅ : Finset (Fin n)) : Set (Fin n)) := by
      intro u v huv
      rw [SimpleGraph.deleteEdges_adj] at huv
      have he_in_E1 : s(u, v) ∈ E1 := Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv.1, huv.2⟩
      rw [hE1_empty] at he_in_E1
      exact absurd he_in_E1 (Finset.notMem_empty _)
    have hT0 : T.card ≤ 0 := hT.2 ∅ hcov_empty
    rw [hE1_empty, Finset.card_empty]
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE1_empty
    have he0_G : e0 ∈ G.edgeFinset := (Finset.mem_sdiff.mp he0).1
    obtain ⟨u0, v0, he0_eq, hu0v0⟩ : ∃ u v : Fin n, e0 = s(u, v) ∧ G.Adj u v := by
      induction e0 using Sym2.ind with
      | _ a b => exact ⟨a, b, rfl, SimpleGraph.mem_edgeFinset.mp he0_G⟩
    have hfun_eq : ∀ x : Fin n → Bool, wval C x C.output = graphFun G ∅ x := by
      intro x
      have hx := congrFun hfun x
      exact hx
    have hout_lt : C.output < n + C.gates.length := by
      by_contra hge
      push Not at hge
      have hfalse := wval_ge_len C (pairInput u0 v0) C.output hge
      have htrue : wval C (pairInput u0 v0) C.output = true := by
        rw [hfun_eq, graphFun_empty_pair_iff]
        exact hu0v0
      rw [hfalse] at htrue
      exact Bool.noConfusion htrue
    have hout_ge : n ≤ C.output := by
      by_contra hlt_n
      push Not at hlt_n
      exact input_not_belowF G C C.output hlt_n (fun x hx => by rw [← hfun_eq]; exact hx)
    let j_out : ℕ := C.output - n
    have hj_out : j_out < C.gates.length := by omega
    have hout_eq : n + j_out = C.output := by omega
    have hbj_out : BelowF G C j_out := by
      intro x hx
      rw [gateVal_eq_wval, hout_eq, hfun_eq] at hx
      exact hx
    let OC : Finset ℕ := orCone n C j_out
    let TopORs : Finset ℕ := OC.filter fun k => (gateAt C k).op = GateOp.or
    let A_top : Finset ℕ := OC.filter fun k => (gateAt C k).op = GateOp.and
    let A_prod : Finset ℕ := A_top.filter fun a =>
      (Vset n C (opnd C a 0)).Nonempty ∧ (Vset n C (opnd C a 1)).Nonempty
    let LeafORs : Finset ℕ := (Finset.range C.gates.length).filter fun k =>
      (gateAt C k).op = GateOp.or ∧ ¬ BelowF G C k
    -- Every gate in A_prod has cross-edges in G and hence one side of size 1
    have hA_prod_adj : ∀ a ∈ A_prod, ∀ x ∈ Vset n C (opnd C a 0), ∀ y ∈ Vset n C (opnd C a 1), G.Adj x y := by
      intro a ha x hx y hy
      have ha_top : a ∈ A_top := (Finset.mem_filter.mp ha).1
      have ha_OC : a ∈ OC := (Finset.mem_filter.mp ha_top).1
      have ha_and : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp ha_top).2
      obtain ⟨ha_le, hba, _⟩ := orCone_props G hAO2 j_out hj_out hbj_out a ha_OC
      have ha_lt : a < C.gates.length := by omega
      obtain ⟨_, _, h0, h1⟩ := ao2_gate_spec hAO2 a ha_lt
      have hx1 : wval C (unitInput x) (opnd C a 0) = true := vset_wval_unit hAO2 _ (by omega) x hx
      have hy1 : wval C (unitInput y) (opnd C a 1) = true := vset_wval_unit hAO2 _ (by omega) y hy
      have hx2 : wval C (pairInput x y) (opnd C a 0) = true :=
        wval_mono hAO2 (fun i hi => by
          have : i = x := of_decide_eq_true hi
          subst this; simp [pairInput]) _ (by omega) hx1
      have hy2 : wval C (pairInput x y) (opnd C a 1) = true :=
        wval_mono hAO2 (fun i hi => by
          have : i = y := of_decide_eq_true hi
          subst this; simp [pairInput]) _ (by omega) hy1
      have hga : gateVal n C a (pairInput x y) = true := by
        rw [gateVal_and hAO2 a ha_lt ha_and, hx2, hy2]; rfl
      exact (graphFun_empty_pair_iff G x y).mp (hba (pairInput x y) hga)
    have hA_prod_one : ∀ a ∈ A_prod,
        (Vset n C (opnd C a 0)).card = 1 ∨ (Vset n C (opnd C a 1)).card = 1 := by
      intro a ha
      have hne := (Finset.mem_filter.mp ha).2
      have hc0 : 1 ≤ (Vset n C (opnd C a 0)).card := Finset.one_le_card.mpr hne.1
      have hc1 : 1 ≤ (Vset n C (opnd C a 1)).card := Finset.one_le_card.mpr hne.2
      by_contra hneither
      push Not at hneither
      have h20 : 1 < (Vset n C (opnd C a 0)).card := by omega
      have h21 : 1 < (Vset n C (opnd C a 1)).card := by omega
      obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp h20
      have hsub : Vset n C (opnd C a 1) ⊆ Finset.univ.filter (fun w => G.Adj x1 w ∧ G.Adj x2 w) := by
        intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hA_prod_adj a ha x1 hx1 y hy, hA_prod_adj a ha x2 hx2 y hy⟩
      have hle := hC4 x1 x2 hxne
      have hle2 := Finset.card_le_card hsub
      omega
    -- Define centre and leafOpnd for each a in A_prod
    let centre : ℕ → Fin n := fun a =>
      if h0 : (Vset n C (opnd C a 0)).card = 1 then
        (Vset n C (opnd C a 0)).min' (Finset.card_pos.mp (by omega))
      else if h1 : (Vset n C (opnd C a 1)).card = 1 then
        (Vset n C (opnd C a 1)).min' (Finset.card_pos.mp (by omega))
      else u0
    let leafOpnd : ℕ → ℕ := fun a =>
      if (Vset n C (opnd C a 0)).card = 1 then opnd C a 1 else opnd C a 0
    have hcentre_spec : ∀ a ∈ A_prod,
        ((Vset n C (opnd C a 0) = {centre a} ∧ leafOpnd a = opnd C a 1) ∨
         (Vset n C (opnd C a 1) = {centre a} ∧ leafOpnd a = opnd C a 0)) ∧
        (∀ y ∈ Vset n C (leafOpnd a), G.Adj (centre a) y) := by
      intro a ha
      rcases hA_prod_one a ha with h0 | h1
      · have hsing := card_eq_one_eq_singleton_min (Vset n C (opnd C a 0)) h0
        have hc : centre a = (Vset n C (opnd C a 0)).min' (Finset.card_pos.mp (by omega)) := by
          dsimp only [centre]; simp only [h0, dite_true]
        have hl : leafOpnd a = opnd C a 1 := by
          dsimp only [leafOpnd]; simp only [h0, ite_true]
        refine ⟨Or.inl ⟨by rw [hc]; exact hsing, hl⟩, ?_⟩
        intro y hy
        rw [hl] at hy
        apply hA_prod_adj a ha (centre a) _ y hy
        rw [hc]; exact Finset.min'_mem _ _
      · by_cases h0 : (Vset n C (opnd C a 0)).card = 1
        · have hsing := card_eq_one_eq_singleton_min (Vset n C (opnd C a 0)) h0
          have hc : centre a = (Vset n C (opnd C a 0)).min' (Finset.card_pos.mp (by omega)) := by
            dsimp only [centre]; simp only [h0, dite_true]
          have hl : leafOpnd a = opnd C a 1 := by
            dsimp only [leafOpnd]; simp only [h0, ite_true]
          refine ⟨Or.inl ⟨by rw [hc]; exact hsing, hl⟩, ?_⟩
          intro y hy
          rw [hl] at hy
          apply hA_prod_adj a ha (centre a) _ y hy
          rw [hc]; exact Finset.min'_mem _ _
        · have hsing := card_eq_one_eq_singleton_min (Vset n C (opnd C a 1)) h1
          have hc : centre a = (Vset n C (opnd C a 1)).min' (Finset.card_pos.mp (by omega)) := by
            dsimp only [centre]; simp only [h0, dite_false, h1, dite_true]
          have hl : leafOpnd a = opnd C a 0 := by
            dsimp only [leafOpnd]; simp only [h0, ite_false]
          refine ⟨Or.inr ⟨by rw [hc]; exact hsing, hl⟩, ?_⟩
          intro y hy
          rw [hl] at hy
          exact (hA_prod_adj a ha y hy (centre a) (by rw [hc]; exact Finset.min'_mem _ _)).symm
    -- Every edge in E1 is covered by some a in A_prod
    have hE1_cover : ∀ e ∈ E1, ∃ a ∈ A_prod, ∃ y ∈ Vset n C (leafOpnd a), e = s(centre a, y) := by
      intro e he
      have heG : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
      have heNotD : e ∉ D_edges := (Finset.mem_sdiff.mp he).2
      obtain ⟨u, v, rfl, huv⟩ : ∃ u v : Fin n, e = s(u, v) ∧ G.Adj u v := by
        induction e using Sym2.ind with
        | _ a b => exact ⟨a, b, rfl, SimpleGraph.mem_edgeFinset.mp heG⟩
      have hne : u ≠ v := G.ne_of_adj huv
      have hnot_rt : ¬ ReadTwiceAt n C j_out u v := by
        intro hrt
        exact heNotD (Finset.mem_filter.mpr ⟨heG, u, v, rfl, hrt⟩)
      unfold ReadTwiceAt readsAtMost at hnot_rt
      have hrm : ((readVectors (atGate n C j_out) n [u.val, v.val] 1).getD (atGate n C j_out).output []).any
          (fun vec => vec.all fun a => decide (a ≤ 1)) = true := by
        cases hval : ((readVectors (atGate n C j_out) n [u.val, v.val] 1).getD (atGate n C j_out).output []).any
            (fun vec => vec.all fun a => decide (a ≤ 1))
        · exact absurd hval hnot_rt
        · rfl
      have hrv_eq : readVectors (atGate n C j_out) n [u.val, v.val] 1 = readVectors C n [u.val, v.val] 1 := rfl
      have hout_at : (atGate n C j_out).output = n + j_out := rfl
      rw [hrv_eq, hout_at, List.any_eq_true] at hrm
      obtain ⟨vec, hvec_mem, hvec_all⟩ := hrm
      obtain ⟨cu, cv, rfl, _, _, hsum⟩ := rv_pair_shape hAO2 u v hne (n + j_out) (by omega) vec hvec_mem
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hvec_all
      have hcu : cu = 1 := by
        by_contra hcu0
        have hcz : cu = 0 := by omega
        subst hcz
        have hv_true := rv_zero_fst_wval hAO2 u v hne (n + j_out) (by omega) cv hvec_mem
        rw [hout_eq, hfun_eq, graphFun_empty_unit] at hv_true
        exact Bool.noConfusion hv_true
      have hcv : cv = 1 := by
        by_contra hcv0
        have hcz : cv = 0 := by omega
        subst hcz
        have hu_true := rv_zero_snd_wval hAO2 u v hne (n + j_out) (by omega) cu hvec_mem
        rw [hout_eq, hfun_eq, graphFun_empty_unit] at hu_true
        exact Bool.noConfusion hu_true
      subst hcu hcv
      obtain ⟨a, ha_OC, ha_and, hside⟩ := descent_to_and G hAO2 u v hne j_out hj_out hbj_out hvec_mem
      have ha_prod : a ∈ A_prod := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ha_OC, ha_and⟩, ?_⟩
        rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
        · exact ⟨⟨u, hu0⟩, ⟨v, hv1⟩⟩
        · exact ⟨⟨v, hv0⟩, ⟨u, hu1⟩⟩
      obtain ⟨hcs, _⟩ := hcentre_spec a ha_prod
      rcases hcs with ⟨hs0, hl1⟩ | ⟨hs1, hl0⟩
      · rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
        · rw [hs0, Finset.mem_singleton] at hu0
          exact ⟨a, ha_prod, v, hl1 ▸ hv1, by rw [hu0]⟩
        · rw [hs0, Finset.mem_singleton] at hv0
          exact ⟨a, ha_prod, u, hl1 ▸ hu1, by rw [hv0, Sym2.eq_swap]⟩
      · rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
        · rw [hs1, Finset.mem_singleton] at hv1
          exact ⟨a, ha_prod, u, hl0 ▸ hu0, by rw [hv1, Sym2.eq_swap]⟩
        · rw [hs1, Finset.mem_singleton] at hu1
          exact ⟨a, ha_prod, v, hl0 ▸ hv0, by rw [hu1]⟩
    -- Bound 1: T.card <= A_prod.card
    let S_centers : Finset (Fin n) := A_prod.image centre
    have hS_cov : G1.IsVertexCover (S_centers : Set (Fin n)) := by
      intro u v huv
      rw [SimpleGraph.deleteEdges_adj] at huv
      have heE1 : s(u, v) ∈ E1 := Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv.1, huv.2⟩
      obtain ⟨a, ha, y, _, heq⟩ := hE1_cover s(u, v) heE1
      have hmem : centre a ∈ s(u, v) := by rw [heq]; exact Sym2.mem_mk_left _ _
      rw [Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl
      · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem centre ha))
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem centre ha))
    have hT_le_A : T.card ≤ A_prod.card :=
      le_trans (hT.2 S_centers hS_cov) Finset.card_image_le
    -- Bound 2: A_prod.card <= TopORs.card + 1
    have hOC_erase_sub : OC.erase j_out ⊆ TopORs.biUnion (fun k => {opnd C k 0 - n, opnd C k 1 - n}) := by
      intro m hm
      obtain ⟨hm_ne, hm_OC⟩ := Finset.mem_erase.mp hm
      obtain ⟨_, _, hpar⟩ := orCone_props G hAO2 j_out hj_out hbj_out m hm_OC
      obtain ⟨k, hk_OC, hkor, hkpar⟩ := hpar hm_ne
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk_OC, hkor⟩, ?_⟩
      rcases hkpar with rfl | rfl <;> simp
    have hOC_card_le : (OC.erase j_out).card ≤ 2 * TopORs.card := by
      calc (OC.erase j_out).card
          ≤ (TopORs.biUnion (fun k => ({opnd C k 0 - n, opnd C k 1 - n} : Finset ℕ))).card :=
            Finset.card_le_card hOC_erase_sub
        _ ≤ ∑ k ∈ TopORs, ({opnd C k 0 - n, opnd C k 1 - n} : Finset ℕ).card := Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ TopORs, 2 := Finset.sum_le_sum fun k _ => by
            calc ({opnd C k 0 - n, opnd C k 1 - n} : Finset ℕ).card
                ≤ ({opnd C k 1 - n} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
              _ = 2 := by simp
        _ = 2 * TopORs.card := by simp [Nat.mul_comm]
    have hTop_disj : Disjoint TopORs A_top := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      have h1 := (Finset.mem_filter.mp hk1).2
      have h2 := (Finset.mem_filter.mp hk2).2
      rw [h1] at h2
      exact GateOp.noConfusion h2
    have hTop_sub_OC : TopORs ∪ A_top ⊆ OC :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hj_mem_OC : j_out ∈ OC := mem_orCone_self C j_out hj_out
    have hA_top_le : A_top.card ≤ TopORs.card + 1 := by
      have h1 : TopORs.card + A_top.card = (TopORs ∪ A_top).card := (Finset.card_union_of_disjoint hTop_disj).symm
      have h2 : (TopORs ∪ A_top).card ≤ OC.card := Finset.card_le_card hTop_sub_OC
      have h3 : (OC.erase j_out).card + 1 = OC.card := Finset.card_erase_add_one hj_mem_OC
      omega
    have hA_prod_le_Top : A_prod.card ≤ TopORs.card + 1 :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hA_top_le
    -- Bound 3: E1.card <= A_prod.card + LeafORs.card
    let Pc : Fin n → Finset ℕ := fun c => A_prod.filter fun a => centre a = c
    let Fc : Fin n → Finset ℕ := fun c => (Pc c).image leafOpnd
    have hFc_bound : ∀ c ∈ S_centers, ∀ w ∈ Fc c, w < n + C.gates.length := by
      intro c _ w hw
      obtain ⟨a, ha_Pc, rfl⟩ := Finset.mem_image.mp hw
      have ha_prod : a ∈ A_prod := (Finset.mem_filter.mp ha_Pc).1
      have ha_OC : a ∈ OC := (Finset.mem_filter.mp (Finset.mem_filter.mp ha_prod).1).1
      obtain ⟨ha_le, _, _⟩ := orCone_props G hAO2 j_out hj_out hbj_out a ha_OC
      obtain ⟨_, _, h0, h1⟩ := ao2_gate_spec hAO2 a (by omega)
      dsimp only [leafOpnd]
      split_ifs <;> omega
    have hReach_adj : ∀ c ∈ S_centers, ∀ y ∈ Reach n C (Fc c), G.Adj c y := by
      intro c _ y hy
      obtain ⟨w, hw_Fc, hyw⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨a, ha_Pc, rfl⟩ := Finset.mem_image.mp hw_Fc
      have ha_prod : a ∈ A_prod := (Finset.mem_filter.mp ha_Pc).1
      have ha_c : centre a = c := (Finset.mem_filter.mp ha_Pc).2
      rw [← ha_c]
      exact (hcentre_spec a ha_prod).2 y hyw
    have hBig_sub_Leaf : ∀ c ∈ S_centers, Big n C (Fc c) ⊆ LeafORs := by
      intro c hc h hh
      obtain ⟨hmem_g, hcard⟩ := Finset.mem_filter.mp hh
      obtain ⟨w, hw_Fc, hhg⟩ := Finset.mem_biUnion.mp hmem_g
      obtain ⟨hlt, _, hhor, _⟩ := gset_props hAO2 w (hFc_bound c hc w hw_Fc) h hhg
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hhor, ?_⟩
      intro hbh
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (Vset n C (n + h)).card)
      have htrue : gateVal n C h (unitInput y) = true := vset_wval_unit hAO2 (n + h) (by omega) y hy
      have hgf := hbh (unitInput y) htrue
      rw [graphFun_empty_unit] at hgf
      exact Bool.noConfusion hgf
    have hBig_disj : (S_centers : Set (Fin n)).PairwiseDisjoint (fun c => Big n C (Fc c)) := by
      intro c1 hc1 c2 hc2 hcne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro h hh1 hh2
      obtain ⟨hmem1, hcard⟩ := Finset.mem_filter.mp hh1
      obtain ⟨hmem2, _⟩ := Finset.mem_filter.mp hh2
      obtain ⟨w1, hw1, hhg1⟩ := Finset.mem_biUnion.mp hmem1
      obtain ⟨w2, hw2, hhg2⟩ := Finset.mem_biUnion.mp hmem2
      obtain ⟨_, _, _, hsub1⟩ := gset_props hAO2 w1 (hFc_bound c1 hc1 w1 hw1) h hhg1
      obtain ⟨_, _, _, hsub2⟩ := gset_props hAO2 w2 (hFc_bound c2 hc2 w2 hw2) h hhg2
      have hsub_cn : Vset n C (n + h) ⊆ Finset.univ.filter (fun y => G.Adj c1 y ∧ G.Adj c2 y) := by
        intro y hy
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_, ?_⟩
        · exact hReach_adj c1 hc1 y (Finset.mem_biUnion.mpr ⟨w1, hw1, hsub1 hy⟩)
        · exact hReach_adj c2 hc2 y (Finset.mem_biUnion.mpr ⟨w2, hw2, hsub2 hy⟩)
      have hle1 := hC4 c1 c2 hcne
      have hle2 := Finset.card_le_card hsub_cn
      omega
    have hE1_sub_stars : E1 ⊆ S_centers.biUnion (fun c => (Reach n C (Fc c)).image (fun y => s(c, y))) := by
      intro e he
      obtain ⟨a, ha_prod, y, hy, rfl⟩ := hE1_cover e he
      refine Finset.mem_biUnion.mpr ⟨centre a, Finset.mem_image_of_mem centre ha_prod, ?_⟩
      refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨leafOpnd a,
        Finset.mem_image_of_mem leafOpnd (Finset.mem_filter.mpr ⟨ha_prod, rfl⟩), hy⟩
    have hsum_Pc : ∑ c ∈ S_centers, (Pc c).card = A_prod.card := by
      have h := Finset.card_eq_sum_card_fiberwise (f := centre) (s := A_prod) (t := S_centers)
        (fun a ha => Finset.mem_image_of_mem centre ha)
      exact h.symm
    have hsum_Big : ∑ c ∈ S_centers, (Big n C (Fc c)).card ≤ LeafORs.card := by
      rw [← Finset.card_biUnion hBig_disj]
      apply Finset.card_le_card
      intro h hh
      obtain ⟨c, hc, hhc⟩ := Finset.mem_biUnion.mp hh
      exact hBig_sub_Leaf c hc hhc
    have hE1_le : E1.card ≤ A_prod.card + LeafORs.card := by
      calc E1.card
          ≤ (S_centers.biUnion (fun c => (Reach n C (Fc c)).image (fun y => s(c, y)))).card :=
            Finset.card_le_card hE1_sub_stars
        _ ≤ ∑ c ∈ S_centers, ((Reach n C (Fc c)).image (fun y => s(c, y))).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ S_centers, (Reach n C (Fc c)).card :=
            Finset.sum_le_sum fun c _ => Finset.card_image_le
        _ ≤ ∑ c ∈ S_centers, ((Fc c).card + (Big n C (Fc c)).card) :=
            Finset.sum_le_sum fun c hc => or_cover_bound hAO2 _ (Fc c) rfl (hFc_bound c hc)
        _ ≤ ∑ c ∈ S_centers, ((Pc c).card + (Big n C (Fc c)).card) :=
            Finset.sum_le_sum fun c _ => Nat.add_le_add_right Finset.card_image_le _
        _ = (∑ c ∈ S_centers, (Pc c).card) + (∑ c ∈ S_centers, (Big n C (Fc c)).card) :=
            Finset.sum_add_distrib
        _ ≤ A_prod.card + LeafORs.card := by omega
    -- Bound 4: Three disjoint ledgers fit inside C.size
    have hTop_range : TopORs ⊆ Finset.range C.gates.length := by
      intro k hk
      obtain ⟨hle, _, _⟩ := orCone_props G hAO2 j_out hj_out hbj_out k (Finset.mem_filter.mp hk).1
      exact Finset.mem_range.mpr (by omega)
    have hA_range : A_prod ⊆ Finset.range C.gates.length := by
      intro k hk
      have hk_OC : k ∈ OC := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
      obtain ⟨hle, _, _⟩ := orCone_props G hAO2 j_out hj_out hbj_out k hk_OC
      exact Finset.mem_range.mpr (by omega)
    have hLeaf_range : LeafORs ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
    have hDisj_TA : Disjoint TopORs A_prod := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      have h1 := (Finset.mem_filter.mp hk1).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk2).1).2
      rw [h1] at h2; exact GateOp.noConfusion h2
    have hDisj_TL : Disjoint TopORs LeafORs := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨_, hbk, _⟩ := orCone_props G hAO2 j_out hj_out hbj_out k (Finset.mem_filter.mp hk1).1
      exact (Finset.mem_filter.mp hk2).2.2 hbk
    have hDisj_AL : Disjoint A_prod LeafORs := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk1).1).2
      have h2 := (Finset.mem_filter.mp hk2).2.1
      rw [h1] at h2; exact GateOp.noConfusion h2
    have hLedgers : TopORs.card + A_prod.card + LeafORs.card ≤ C.size := by
      have h1 : Disjoint (TopORs ∪ A_prod) LeafORs := Finset.disjoint_union_left.mpr ⟨hDisj_TL, hDisj_AL⟩
      have h2 : (TopORs ∪ A_prod ∪ LeafORs).card = TopORs.card + A_prod.card + LeafORs.card := by
        rw [Finset.card_union_of_disjoint h1, Finset.card_union_of_disjoint hDisj_TA]
      have h3 : TopORs ∪ A_prod ∪ LeafORs ⊆ Finset.range C.gates.length :=
        Finset.union_subset (Finset.union_subset hTop_range hA_range) hLeaf_range
      have h4 := Finset.card_le_card h3
      rw [Finset.card_range] at h4
      change TopORs.card + A_prod.card + LeafORs.card ≤ C.gates.length
      omega
    omega

end PEqualNP.Outside.L_meta_3706_aux

theorem PEqualNP.Outside.L_meta_3706 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)),
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ((G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)) : Set (Sym2 (Fin n)))) T →
      G.edgeFinset.card + T.card ≤ C.size + (G.edgeFinset.filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧ PEqualNP.Core.ReadTwiceAt n C (C.output - n) u v)).card + 1 :=
  PEqualNP.Outside.L_meta_3706_aux.d_ledger_main
