import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467_aux

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

private lemma foldl_wires_getD_lt (f : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (acc : List Bool) (i : ℕ), i < acc.length →
      (gs.foldl (fun w g => w ++ [f w g]) acc).getD i false = acc.getD i false := by
  induction gs with
  | nil => intro acc i _; rfl
  | cons g gs ih =>
    intro acc i hi
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [f acc g]).length := by simp; omega
    rw [ih _ i hi']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wires_getD_lt (C : Circuit) (inp : List Bool) (i : ℕ) (hi : i < inp.length) :
    (C.wires inp).getD i false = inp.getD i false := by
  unfold Circuit.wires
  exact foldl_wires_getD_lt _ C.gates inp i hi

private lemma incidenceInput_len {n : ℕ} (X Y : Finset (Fin n)) :
    (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

private lemma incidenceInput_getD_left {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
  unfold incidenceInput
  have h1 : i < (List.ofFn (fun p : Fin n => decide (p ∈ X))).length := by simp [hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  simp [hi]

private lemma incidenceInput_getD_right {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ)
    (hlo : n ≤ i) (hhi : i < n + n) :
    (incidenceInput X Y).getD i false = decide (⟨i - n, by omega⟩ ∈ Y) := by
  unfold incidenceInput
  have hlen : (List.ofFn (fun p : Fin n => decide (p ∈ X))).length = n := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  have hsub : i - n < n := by omega
  simp [hsub]

end PEqualNP.Outside.L_meta_3467_aux

theorem PEqualNP.Outside.L_meta_3467 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq _ _ _ _ hout _ hfalse
  exfalso
  by_cases hlt : C.output < n
  · let p : Fin n := ⟨C.output, hlt⟩
    have hf := hfalse {p} ∅ (by simp) (by intro l hl; simp at hl)
    have hev : C.eval (PEqualNP.GenericRejection.incidenceInput ({p} : Finset (Fin n)) (∅ : Finset (Fin n))) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [PEqualNP.Outside.L_meta_3467_aux.wires_getD_lt C _ C.output
            (by rw [PEqualNP.Outside.L_meta_3467_aux.incidenceInput_len]; exact hout)]
      rw [PEqualNP.Outside.L_meta_3467_aux.incidenceInput_getD_left _ _ C.output hlt]
      simp [p]
    rw [hev] at hf
    exact Bool.noConfusion hf
  · let l : Fin n := ⟨C.output - n, by omega⟩
    have hf := hfalse ∅ {l} (by simp; omega) (by intro k _; exact Finset.disjoint_empty_right _)
    have hev : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin n)) ({l} : Finset (Fin n))) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [PEqualNP.Outside.L_meta_3467_aux.wires_getD_lt C _ C.output
            (by rw [PEqualNP.Outside.L_meta_3467_aux.incidenceInput_len]; exact hout)]
      rw [PEqualNP.Outside.L_meta_3467_aux.incidenceInput_getD_right _ _ C.output (by omega) hout]
      simp [l]
    rw [hev] at hf
    exact Bool.noConfusion hf
