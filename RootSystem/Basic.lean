import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Reduced


variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j : ι}


namespace RootPairing
lemma name? (hP : IsReduced P) (i j : ι) (h : ¬ LinearIndependent R ![P.coroot i, P.coroot j]) :
    P.coroot i = P.coroot j ∨ P.coroot i = - P.coroot j := sorry

lemma flip_still_reduced (hP : IsReduced P) : IsReduced (P.flip) := by
    intro i j h
    have key : P.flip.root = P.coroot := rfl
    rw [key]
    exact name? P hP i j h

#print RootPairing.flip_still_reduced


end RootPairing
