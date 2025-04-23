import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j k : ι}

namespace RootPairing

-- Define an instance of a perfect pairing?


lemma reflection_perm_unique {Q : RootPairing ι R M N} {h1 : Q.toPerfectPairing = P.toPerfectPairing} {h2 : Q.root = P.root} {h3 : Q.coroot = P.coroot} :
    Q.reflection_perm = P.reflection_perm := by
  ext i j
  apply P.root.injective
  nth_rewrite 1 [← h2]
  rw [← Q.reflection_perm_root, ← P.reflection_perm_root, h1, h2, h3]


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
-- Prove that the pairing is invariant under the Weyl group


end RootPairing
