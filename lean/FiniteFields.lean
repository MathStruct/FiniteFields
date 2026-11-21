import Mathlib.Algebra.Field.ZMod
import FiniteFields.RankEncoding
import FiniteFields.NimberDigits
import FiniteFields.NimberTower

namespace FiniteFields

/-- Mathlib already provides the field structure on `ZMod p` for prime `p`. -/
example (p : ℕ) [Fact p.Prime] : Field (ZMod p) := inferInstance

end FiniteFields
