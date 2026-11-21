/-
Tower digits are binary digits: DiMuro's Lemma 1.1 on CombinatorialGames' `Nimber` (backlog R3).

The R1 computation (`research/nimber_closure/`) writes an element of a finite tower
`L ⊂ On₂` as a nim-sum of *tower monomials* `g_k ^ e_k * ⋯ * g_1 ^ e_1 * ∗2 ^ i`
(`e_j < u_j`, `∗2 ^ i` a bit of the base field), and computes the reduced echelon basis of every
`𝔽_{2^n} ⊂ L` for the order "largest monomial first (exponent of `g_k` first, …), then the bit".
`NimberDigits.nimSum_lt_of_rank_lt` needs a reduced echelon basis for *binary* digits. This file
proves that the two agree:

* `mono_eq` (DiMuro's Lemma 1.1, monomial form): if every generator `g_j = ∗2 ^ a_j` is a ring
  whose `leastNoRoots` has degree at least `u_j`, and the generators grow fast enough
  (`a_{j+1} ≥ a_j * u_j`, the base bits `i < a_1`), the nim-monomial is the single binary digit
  `∗2 ^ (a_k * e_k + ⋯ + a_1 * e_1 + i)` (ordinal arithmetic). One step is CombinatorialGames'
  `IsRing.pow_mul_eq`.
* `exp_lt_exp_iff`: that exponent, as a function of the tower digit, is strictly increasing for
  the lexicographic order on `(e_k, …, e_1, i)` (Cantor normal form base `2 ^ a_j`).
* `digits_elem`, `elem_add`, `elem_lt_elem_iff`: a tower element is the set of its tower digits;
  nim-addition is their symmetric difference and the ordinal order is their colex order.
* `elem_lt_of_rank_lt`: the rank encoding computed with tower digits is order-preserving.

Not proved here (inputs, as hypotheses of `IsTower`): that the concrete generators of
DiMuro's Theorem 3.1 (the `χ_r`, Lenstra's `α_u`) are rings with the stated `leastNoRoots`.
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic
import FiniteFields.NimberDigits

namespace FiniteFields.NimberTower

open Ordinal Nimber Polynomial Finset Finset.Colex NimberDigits
open scoped symmDiff

/-! ### Towers and tower digits

A tower is a list `[(a_k, u_k), …, (a_1, u_1)]`, from the top: the generator `g_j = ∗2 ^ a_j` of
degree `u_j`. `b₀` bounds the bits of the base field (`b₀ = 2 ^ m` for the base `∗2 ^ 2 ^ m`).
A tower digit is a list of exponents `[e_k, …, e_1]` and a bit `i`. -/

/-- The bound on the binary exponents of tower monomials: `a_k * u_k` (or `b₀` without
generators). -/
def bound (b₀ : Ordinal) : List (Ordinal × ℕ) → Ordinal
  | [] => b₀
  | (a, u) :: _ => a * u

/-- The hypotheses on a tower: each generator `∗2 ^ a` is a ring, `X ^ u ≤ leastNoRoots` (so
polynomials of degree `< u` evaluate as ordinals, `IsRing.eval_eq_of_lt`), and it lies above the
tower below it. For the towers of DiMuro's Theorem 3.1 these are inputs, not proved here. -/
def IsTower (b₀ : Ordinal) : List (Ordinal × ℕ) → Prop
  | [] => True
  | (a, u) :: T => IsRing (∗(2 ^ a)) ∧ (WithTop.some (X ^ u) ≤ leastNoRoots (∗(2 ^ a))) ∧
      bound b₀ T ≤ a ∧ IsTower b₀ T

/-- A valid tower digit: one exponent `e_j < u_j` per generator, and a bit `i < b₀`. -/
def Valid (b₀ : Ordinal) : List (Ordinal × ℕ) → List ℕ → Ordinal → Prop
  | [], [], i => i < b₀
  | (_, u) :: T, e :: es, i => e < u ∧ Valid b₀ T es i
  | _, _, _ => False

/-- The binary exponent of a tower digit: `a_k * e_k + ⋯ + a_1 * e_1 + i`. -/
def exp : List (Ordinal × ℕ) → List ℕ → Ordinal → Ordinal
  | [], _, i => i
  | _ :: _, [], i => i
  | (a, _) :: T, e :: es, i => a * e + exp T es i

/-- The tower monomial `g_k ^ e_k * ⋯ * g_1 ^ e_1 * ∗2 ^ i`, in nimber arithmetic. -/
noncomputable def mono : List (Ordinal × ℕ) → List ℕ → Ordinal → Nimber
  | [], _, i => ∗(2 ^ i)
  | _ :: _, [], i => ∗(2 ^ i)
  | (a, _) :: T, e :: es, i => (∗(2 ^ a)) ^ e * mono T es i

variable {b₀ : Ordinal}

theorem exp_lt_bound {T : List (Ordinal × ℕ)} {es : List ℕ} {i : Ordinal}
    (hT : IsTower b₀ T) (h : Valid b₀ T es i) : exp T es i < bound b₀ T := by
  induction T generalizing es with
  | nil =>
    cases es with
    | nil => exact h
    | cons => exact h.elim
  | cons g T IH =>
    obtain ⟨a, u⟩ := g
    cases es with
    | nil => exact h.elim
    | cons e es =>
      obtain ⟨-, -, hb, hT⟩ := hT
      exact mul_add_lt ((IH hT h.2).trans_le hb) (by exact_mod_cast h.1)

/-- **DiMuro's Lemma 1.1, monomial form.** A tower monomial is the single binary digit
`∗2 ^ (a_k * e_k + ⋯ + a_1 * e_1 + i)`. -/
theorem mono_eq {T : List (Ordinal × ℕ)} {es : List ℕ} {i : Ordinal}
    (hT : IsTower b₀ T) (h : Valid b₀ T es i) : mono T es i = ∗(2 ^ exp T es i) := by
  induction T generalizing es with
  | nil =>
    cases es with
    | nil => rfl
    | cons => exact h.elim
  | cons g T IH =>
    obtain ⟨a, u⟩ := g
    cases es with
    | nil => exact h.elim
    | cons e es =>
      obtain ⟨hr, hl, hb, hT'⟩ := hT
      have ht : exp T es i < a := (exp_lt_bound hT' h.2).trans_le hb
      have hle : WithTop.some ((X : Nimber[X]) ^ (e + 1)) ≤ leastNoRoots (∗(2 ^ a)) :=
        hl.trans' (WithTop.coe_le_coe.2 (Lex.X_pow_le_X_pow_iff.2 h.1))
      have hy : ∗(2 ^ exp T es i) < ∗(2 ^ a) := by
        rw [of.lt_iff_lt]; exact (opow_lt_opow_iff_right one_lt_two).2 ht
      show (∗(2 ^ a)) ^ e * mono T es i = ∗(2 ^ (a * e + exp T es i))
      rw [IH hT' h.2, hr.pow_mul_eq hle hy, val_of, val_of, opow_add, opow_mul, opow_natCast]

/-- **The binary exponent orders tower digits lexicographically**: exponent of the top generator
first, then the next one, …, then the bit (Cantor normal form base `2 ^ a_j`). -/
theorem exp_lt_exp_of_lt {T : List (Ordinal × ℕ)} {es es' : List ℕ} {i i' : Ordinal}
    (hT : IsTower b₀ T) (h : Valid b₀ T es i) (h' : Valid b₀ T es' i')
    (hlt : toLex (es, i) < toLex (es', i')) : exp T es i < exp T es' i' := by
  induction T generalizing es es' with
  | nil =>
    cases es with
    | cons => exact h.elim
    | nil =>
      cases es' with
      | cons => exact h'.elim
      | nil =>
        rw [Prod.Lex.toLex_lt_toLex] at hlt
        show i < i'
        simpa using hlt
  | cons g T IH =>
    obtain ⟨a, u⟩ := g
    cases es with
    | nil => exact h.elim
    | cons e es =>
      cases es' with
      | nil => exact h'.elim
      | cons e' es' =>
        have hT' := hT.2.2.2
        have ha : exp T es i < a := (exp_lt_bound hT' h.2).trans_le hT.2.2.1
        show a * e + exp T es i < a * e' + exp T es' i'
        rw [Prod.Lex.toLex_lt_toLex, List.cons_lt_cons_iff, List.cons.injEq] at hlt
        rcases hlt with (he | ⟨rfl, hs⟩) | ⟨⟨rfl, rfl⟩, hi⟩
        · exact (mul_add_lt ha (Nat.cast_lt.2 he : (e : Ordinal) < e')).trans_le le_self_add
        · exact (add_lt_add_iff_left _).2 (IH hT' h.2 h'.2 (Prod.Lex.toLex_lt_toLex.2 (.inl hs)))
        · exact (add_lt_add_iff_left _).2
            (IH hT' h.2 h'.2 (Prod.Lex.toLex_lt_toLex.2 (.inr ⟨rfl, hi⟩)))

/-- The type of valid tower digits of `T`, ordered lexicographically. -/
def Digit (b₀ : Ordinal) (T : List (Ordinal × ℕ)) :=
  {d : Lex (List ℕ × Ordinal) // Valid b₀ T (ofLex d).1 (ofLex d).2}

noncomputable instance (T : List (Ordinal × ℕ)) : LinearOrder (Digit b₀ T) := Subtype.instLinearOrder _

/-- The binary exponent of a tower digit. -/
def Digit.exp {T : List (Ordinal × ℕ)} (d : Digit b₀ T) : Ordinal :=
  NimberTower.exp T (ofLex d.1).1 (ofLex d.1).2

/-- The tower monomial of a tower digit. -/
noncomputable def Digit.mono {T : List (Ordinal × ℕ)} (d : Digit b₀ T) : Nimber :=
  NimberTower.mono T (ofLex d.1).1 (ofLex d.1).2

theorem Digit.exp_strictMono {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T) :
    StrictMono (Digit.exp (b₀ := b₀) (T := T)) := fun d d' h =>
  exp_lt_exp_of_lt hT d.2 d'.2 h

theorem exp_lt_exp_iff {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T) {d d' : Digit b₀ T} :
    d.exp < d'.exp ↔ d < d' :=
  (Digit.exp_strictMono hT).lt_iff_lt

theorem Digit.mono_eq {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T) (d : Digit b₀ T) :
    d.mono = ∗(2 ^ d.exp) :=
  NimberTower.mono_eq hT d.2

/-! ### Tower elements are sets of tower digits -/

/-- The element of the tower with the tower digits `D`: the nim-sum of their monomials. -/
noncomputable def elem {T : List (Ordinal × ℕ)} (D : Finset (Digit b₀ T)) : Nimber :=
  ∑ d ∈ D, d.mono

theorem elem_eq_ofDigits {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T) (D : Finset (Digit b₀ T)) :
    elem D = ofDigits (D.image Digit.exp) := by
  rw [elem, ofDigits, sum_image fun d _ d' _ h => (Digit.exp_strictMono hT).injective h]
  exact sum_congr rfl fun d _ => d.mono_eq hT

/-- **The binary digits of a tower element are the binary exponents of its tower digits.** -/
theorem digits_elem {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T) (D : Finset (Digit b₀ T)) :
    digits (elem D).val = D.image Digit.exp := by
  rw [elem_eq_ofDigits hT, digits_ofDigits]

/-- Nim-addition is the symmetric difference of tower digits. -/
theorem elem_add {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T) (D D' : Finset (Digit b₀ T)) :
    elem D + elem D' = elem (D ∆ D') := by
  rw [elem_eq_ofDigits hT, elem_eq_ofDigits hT, elem_eq_ofDigits hT, ofDigits_add,
    image_symmDiff D D' (Digit.exp_strictMono hT).injective]

/-- **The ordinal order on tower elements is the colex order of their tower digits.** -/
theorem elem_lt_elem_iff {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T)
    {D D' : Finset (Digit b₀ T)} : elem D < elem D' ↔ toColex D < toColex D' := by
  rw [← val.lt_iff_lt, ← digits_strictMono.lt_iff_lt, digits_elem hT, digits_elem hT,
    toColex_image_lt_toColex_image (Digit.exp_strictMono hT)]

/-- **The rank encoding computed with tower digits is order-preserving.** Let `D 0, D 1, …` be
the tower digit sets of a reduced echelon family *for the tower order* (the largest tower digits
increase strictly, and the largest tower digit of `D i` is not in any other `D j`), as computed
by R1 for the echelon basis of `𝔽_{2^n} ⊂ L`. Then the nim-sum of the elements `elem (D i)`,
`i ∈ e`, increases strictly with the rank `∑_{i ∈ e} 2 ^ i`. -/
theorem elem_lt_of_rank_lt {T : List (Ordinal × ℕ)} (hT : IsTower b₀ T)
    (D : ℕ → Finset (Digit b₀ T)) (hne : ∀ i, (D i).Nonempty)
    (hp : StrictMono fun i => (D i).max' (hne i))
    (hred : ∀ i j, i ≠ j → (D i).max' (hne i) ∉ D j)
    {e e' : Finset ℕ} (h : ∑ i ∈ e, (2 : ℕ) ^ i < ∑ i ∈ e', (2 : ℕ) ^ i) :
    ∑ i ∈ e, elem (D i) < ∑ i ∈ e', elem (D i) := by
  have hm := Digit.exp_strictMono hT
  have hne' : ∀ i, (digits (elem (D i)).val).Nonempty := fun i => by
    rw [digits_elem hT]; exact (hne i).image _
  have hmax : ∀ i, (digits (elem (D i)).val).max' (hne' i) = ((D i).max' (hne i)).exp := by
    intro i
    simp_rw [digits_elem hT]
    exact max'_image hm.monotone _ _
  refine nimSum_lt_of_rank_lt (fun i => elem (D i)) hne' ?_ ?_ h
  · intro i j hij
    simp only [hmax]
    exact hm (hp hij)
  · intro i j hij
    rw [hmax i, digits_elem hT, mem_image]
    rintro ⟨d, hd, hde⟩
    exact hred i j hij (hm.injective hde ▸ hd)

/-! ### A concrete tower: `𝔽₄ = 𝔽₂(∗2)` -/

/-- The hypotheses are satisfiable: the one-step tower with generator `∗2 = ∗2 ^ 1` of degree 2
over the bits of `𝔽₂` (`b₀ = 1`), i.e. `𝔽₄` with tower digits `([e], 0)`, `e < 2`. -/
theorem isTower_F4 : IsTower 1 [((1 : Ordinal), 2)] := by
  refine ⟨?_, ?_, le_rfl, trivial⟩ <;> rw [opow_one]
  · exact IsField.two.toIsRing
  · exact IsField.two.X_sq_lt_leastNoRoots.le

end FiniteFields.NimberTower
