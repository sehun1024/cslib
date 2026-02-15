module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

public section

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

universe u

variable {Var : Type u}

/-!

This section is for the alternative and more useful definition for the "locally closed".

-/

/-- Alternative Definitions for LC
This function counts the actually looks for the binding variables
```
  lc_at 0 M =M.LC
```
-/
@[simp]
def lc_at (k : ℕ) (M : Term Var):Prop :=
match M with
| Term.bvar i => i<k
| Term.fvar _ => True
| Term.app t₁ t₂ => lc_at k t₁ ∧ lc_at k t₂
| Term.abs t => lc_at (k+1) t

/-- This function counts the maximum number of the lambda that is enclosing variables. -/
@[simp]
def depth (M : Term Var) : ℕ :=
match M with
| Term.bvar _ => 0
| Term.fvar _ => 0
| Term.app t₁ t₂ => Nat.max (depth t₁) (depth t₂)
| Term.abs t => depth t +1


protected lemma ind_on_depth (P : Term Var → Prop)
(h1 : ∀ i, P (bvar i))
(h2 : ∀ x, P (fvar x))
(h3 : ∀ M N, P M → P N → P (app M N))
(h4 : ∀ M, P M → (∀ N, depth N ≤ depth M → P N) → P M.abs)
: ∀ M, P M := by
  have h : ∀ (d: ℕ) (M:Term Var), depth M ≤ d → P M := by
    intros d;induction d
    case zero =>
      intros M h5
      induction M
      case bvar => solve_by_elim
      case fvar => solve_by_elim
      case abs M' p => simp at h5
      case app x y p q=>
        simp at h5
        grind
    case succ m h' =>
      intros M p;induction M
      case bvar => solve_by_elim
      case fvar => solve_by_elim
      case abs M' q =>
        simp at p
        apply h4 M'
        · apply q;grind
        · intros N h2
          have h3: depth N ≤ m := by grind
          exact h' N h3
      case app x y q r =>
        simp only [depth, sup_le_iff] at p
        exact h3 _ _ (q p.1) (r p.2)
  exact (fun M ↦ h (depth M) M (by constructor))


/-- The depth of the lambda expression doesn't change by opening at i-th bound variable
 for some free variable. -/
lemma depth_eq_depth_openRec_fvar (M : Term Var) (x : Var) :
∀ (i : ℕ), depth (@openRec Var i (fvar x) M)= depth M := by
  induction M
  case bvar j =>
    intros i;simp only [depth, openRec]
    have h : (if i = j then fvar x else bvar j) = fvar x
      ∨ (if i = j then fvar x else bvar j) = bvar j := ite_eq_or_eq _ _ _
    induction h
    case inl h' => rw [h'];rfl
    case inr h' => rw [h'];rfl
  case fvar y => intros i;simp only [depth, openRec]
  case app t₁ t₂ p₁ p₂ =>
    intros i;simp only [depth, openRec]
    rw [p₁,p₂]
  case abs t p =>
    intros i;simp only [depth, openRec, Nat.add_right_cancel_iff]
    exact p (i+1)

/-- The depth of the lambda expression doesn't change by opening for some free variable. -/
theorem depth_eq_depth_open_fvar (M : Term Var) (x : Var) :
depth (M ^ fvar x) = depth M := depth_eq_depth_openRec_fvar M x 0


/-- Opening for some free variable at i-th bound variable, increases the lc_at by 1. -/
theorem lc_at_iff_lc_at_openRec_fvar (M : Term Var) (x : Var) (i : ℕ) :
  lc_at (i+1) M ↔ lc_at i (@openRec Var i (fvar x) M)
:= by
  revert i
  induction M
  case bvar k =>
    intros i; simp only [lc_at, Order.lt_add_one_iff]
    simp only [openRec]
    have p1:= ite_eq_iff.mp (@rfl _ (if i = k then fvar x else bvar k))
    obtain ⟨p2,p3⟩|⟨p2,p3⟩ := p1
    · rw [← p3];simp;grind
    · rw [← p3];simp;grind
  case fvar x =>
    simp only [openRec]
    intros;simp
  case app x y p q =>
    simp only [openRec,lc_at]
    intros i
    grind
  case abs M p =>
    intros i
    simp only [lc_at]
    solve_by_elim


/-- Opening for some free variable is locally closed if and only if M is lc_at 1. -/
theorem lc_at_iff_lc_at_open_fvar (M : Term Var) (x : Var) :
  lc_at 1 M ↔ lc_at 0 (M ^ (fvar x)) := lc_at_iff_lc_at_openRec_fvar M x 0


/-- M is lc_at 0 if and only if M is locallly closed -/
theorem lc_at_iff_LC (M : Term Var) [hF : HasFresh Var] : lc_at 0 M ↔ M.LC := by
  apply LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth (fun M ↦ lc_at 0 M ↔ M.LC )
  case h1 =>
    simp only [lc_at, not_lt_zero, false_iff];intros i p
    rcases p
  case h2 =>
    simp only [lc_at, true_iff];intros x
    constructor
  case h3 =>
    simp only [lc_at];intros M N p q
    constructor
    · intros h
      constructor
      · grind
      · grind
    · intros h
      rcases h with ⟨h1,h2 ⟩
      grind
  case h4 =>
  intros M' ha1 ha2
  simp only [lc_at, zero_add]
  constructor
  · intros h2
    apply LC.abs ∅
    intros x _
    have ha3 := lc_at_iff_lc_at_openRec_fvar M' x 0
    simp at ha3
    have ha4 := depth_eq_depth_open_fvar M' x
    exact (ha2 (M' ^ fvar x) (by grind)).mp (ha3.mp h2)
  · intros h2
    rcases h2 with ⟨⟩|⟨L,_,q⟩
    let y:= hF.fresh L
    let h3 := hF.fresh_notMem L
    have h4 := q y h3
    have h5 : depth (M' ^ fvar y) = depth M' := by
      simp only [open']
      rw [depth_eq_depth_openRec_fvar M' y]
    have h6 := (ha2 (M' ^ fvar y) (by grind))
    have h7 := h6.mpr h4
    rw [lc_at_iff_lc_at_openRec_fvar M' y]
    exact h7

end Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
