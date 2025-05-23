import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j k : ι}

#check IsSMulRegular
#check RootPairing.reflection_perm_eq_reflection_perm_iff_of_isSMulRegular
namespace RootPairing

-- This is a terrible proof
lemma pairing_si_invariant : P.pairing (P.reflection_perm k i) (P.reflection_perm k j) = P.pairing i j := by
  rw [← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing]
  rw [← P.reflection_perm_root, ← P.reflection_perm_coroot]
  simp
  have key : P.pairing k j - P.pairing k j * 2 = - P.pairing k j := by ring
  have key2 : P.pairing i k * -P.pairing k j = - P.pairing i k * P.pairing k j := by ring
  have key3 : P.pairing i j - P.pairing k j * P.pairing i k = P.pairing i j + - P.pairing k j * P.pairing i k := by ring
  rw [key,key2,key3]
  simp
  rw [add_assoc,mul_comm]
  simp

variable (w : P.weylGroup)
#check w
-- Prove that the pairing is invariant under the Weyl group



end RootPairing
