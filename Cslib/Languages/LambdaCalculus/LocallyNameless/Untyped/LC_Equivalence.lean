/-
Copyright (c) 2026 Elimia (Sehun Kim). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elimia (Sehun Kim)
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

public section

/-!

This section is for the alternative and more useful definition for the "locally closed".
The equivalence of the definitions will be proven in this section.

-/

namespace Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

universe u

variable {Var : Type u}

/-- Alternative Definitions for LC

LcAt k M is satisfied when all bound indices of M are smaller than k.
When k = 0, this is equivalent to LC, as shown in lcAt_iff_LC.
-/
@[simp, scoped grind =]
def lcAt (k : ℕ) : Term Var → Prop
| bvar i => i < k
| fvar _ => True
| app t₁ t₂ => lcAt k t₁ ∧ lcAt k t₂
| abs t => lcAt (k + 1) t

/-- depth counts the maximum number of the lambdas that are enclosing variables. -/
@[simp, scoped grind =]
def depth : Term Var → ℕ
| bvar _ => 0
| fvar _ => 0
| app t₁ t₂ => max (depth t₁) (depth t₂)
| abs t => depth t + 1

@[elab_as_elim]
protected lemma ind_on_depth (P : Term Var → Prop)
(h_bvar : ∀ i, P (bvar i))
(h_fvar : ∀ x, P (fvar x))
(h_app : ∀ M N, P M → P N → P (app M N))
(h_abs : ∀ M, P M → (∀ N, N.depth ≤ M.depth → P N) → P M.abs)
: ∀ M, P M := by
  have h : ∀ (d: ℕ) (M:Term Var), M.depth ≤ d → P M := by
    intros d;induction d
    case zero =>
      intros M;induction M <;>grind
    case succ m h' =>
      intros M p;induction M with
      | abs M' q =>
        apply h_abs M'
        · grind
        · intros N h2
          have h3: N.depth ≤ m := by grind
          exact h' N h3
      | app x y q r =>
        simp only [depth, sup_le_iff] at p
        exact h_app _ _ (q p.1) (r p.2)
      | _ => grind
  exact (fun M ↦ h (depth M) M (by constructor))

/-- The depth of the lambda expression doesn't change by opening at i-th bound variable
 for some free variable. -/
 @[simp, scoped grind .]
lemma depth_openRec_fvar_eq_depth (M : Term Var) (x : Var) (i : ℕ) :
    (M⟦i ↝ fvar x⟧).depth = M.depth := by
  induction M generalizing i <;> grind

/-- The depth of the lambda expression doesn't change by opening for some free variable. -/
theorem depth_open_fvar_eq_depth (M : Term Var) (x : Var) :
  depth (M ^ fvar x) = depth M := depth_openRec_fvar_eq_depth M x 0

/-- Opening for some free variable at i-th bound variable, increases the lcAt by 1. -/
@[simp, scoped grind .]
theorem lcAt_openRec_fvar_iff_lcAt (M : Term Var) (x : Var) (i : ℕ) :
    lcAt i (M⟦i ↝ fvar x⟧) ↔ lcAt (i+1) M := by
  induction M generalizing i <;> grind

/-- Opening for some free variable is locally closed if and only if M is lcAt 1. -/
theorem lcAt_open_fvar_iff_lcAt (M : Term Var) (x : Var) :
   lcAt 0 (M ^ (fvar x)) ↔ lcAt 1 M := lcAt_openRec_fvar_iff_lcAt M x 0

/-- M is lcAt 0 if and only if M is locallly closed. -/
theorem lcAt_iff_LC (M : Term Var) [HasFresh Var] : lcAt 0 M ↔ M.LC := by
induction M using LambdaCalculus.LocallyNameless.Untyped.Term.ind_on_depth with
  | h_abs =>
    constructor
    · grind [LC.abs ∅]
    · intros h2
      rcases h2 with ⟨⟩|⟨L,_,_⟩
      grind [fresh_exists L]
  | _ => grind [cases LC]

end Cslib.LambdaCalculus.LocallyNameless.Untyped.Term
