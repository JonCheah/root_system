import Mathlib.LinearAlgebra.RootSystem.Defs

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j k : ι}

namespace RootPairing

lemma pairing_W_invariant : P.pairing (P.reflection_perm k i) (P.reflection_perm k j) = P.pairing i j := by sorry




end RootPairing
