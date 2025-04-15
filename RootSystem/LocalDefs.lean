import Mathlib.LinearAlgebra.RootSystem.Defs

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j k : ι}

namespace RootPairing

-- This is a terrible proof
lemma pairing_W_invariant : P.pairing (P.reflection_perm k i) (P.reflection_perm k j) = P.pairing i j := by
  rw [← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing]
  rw [← P.reflection_perm_root, ← P.reflection_perm_coroot]
  simp
  have key : P.pairing k j - P.pairing k j * 2 = - P.pairing k j := by ring
  rw [key]
  have key2 : P.pairing i k * -P.pairing k j = - P.pairing i k * P.pairing k j := by ring
  rw [key2]
  simp
  have key3 : P.pairing i j - P.pairing k j * P.pairing i k = P.pairing i j + - P.pairing k j * P.pairing i k := by ring
  rw [key3]
  rw [add_assoc]
  simp
  rw [mul_comm]
  simp




end RootPairing
