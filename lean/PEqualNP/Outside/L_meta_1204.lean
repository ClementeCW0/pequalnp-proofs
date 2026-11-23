import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1204

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [4, 5]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [9, 10]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 14]⟩]
  output := 18

lemma evaluates : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1204

open PEqualNP.Outside.L_meta_1204

theorem PEqualNP.Outside.L_meta_1204 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) ||
        (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, circuit]
  · decide
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact evaluates (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
