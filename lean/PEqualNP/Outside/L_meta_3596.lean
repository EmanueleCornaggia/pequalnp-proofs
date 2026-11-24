import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3596_aux

open PEqualNP.CircuitLowerBounds

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

end PEqualNP.Outside.L_meta_3596_aux

theorem PEqualNP.Outside.L_meta_3596 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C hq _ _ _ _ hout _ _ hsound
  exfalso
  let z : Fin (N + N) → Bool := fun i => decide (i.val = C.output)
  have hcard : Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q := by
    have hle1 : Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro a b
      have ha := a.2
      have hb := b.2
      simp only [z, Fin.val_natAdd, decide_eq_true_eq] at ha hb
      exact Subtype.ext (Fin.ext (by omega))
    omega
  have hno : ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    rintro ⟨p, l, _, hp, hl⟩
    simp only [z, Fin.val_castAdd, Fin.val_natAdd, decide_eq_true_eq] at hp hl
    have := p.isLt
    omega
  have hf := hsound z hcard hno
  have ht : PEqualNP.MetaComplexity.circuitFun (N + N) C z = true := by
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_3596_aux.wires_getD_lt C (List.ofFn z) C.output (by simp [hout])]
    simp [List.getD_eq_getElem?_getD, hout, z]
  rw [ht] at hf
  exact Bool.noConfusion hf
