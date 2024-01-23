import Aesop
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.CompleteLattice
import Mathlib.Logic.Embedding.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

section
universe u

@[aesop unsafe 50%]
def card_greater_noninjective (α β : Type u) (f : α -> β) :
    Cardinal.mk α > Cardinal.mk β -> ¬Function.Injective f := by 
  intro
  have hneq : ¬ Cardinal.mk α <= Cardinal.mk β := by simp_all only [not_le]
  have : ¬Nonempty (α ↪ β) := by
    intro hne
    have : Cardinal.mk α <= Cardinal.mk β := by
      simp_all only [not_le]
      exact hne
    contradiction
  intro hinj
  have : Nonempty (α ↪ β) := Nonempty.intro (Function.Embedding.mk f hinj)
  contradiction

@[aesop unsafe 50%]
def setcomp_elim {α β : Type u} (f : α -> β) (p : α -> Prop) (fx : β) :
    fx ∈ Set.image f {x | p x} -> ∃ x, p x ∧ fx = f x:= by
  intro a
  simp_all only [Set.mem_image, Set.mem_setOf_eq]
  unhygienic with_reducible aesop_destruct_products
  aesop_subst right
  apply Exists.intro
  apply And.intro
  on_goal 2 => apply Eq.refl
  simp_all only

@[aesop unsafe 50%]
def setcomp_intro {α β : Type u} (f : α -> β) (p : α -> Prop) (x : α) :
    p x -> f x ∈ Set.image f {x | p x} := by
  intro a
  simp_all only [Set.mem_image, Set.mem_setOf_eq]
  apply Exists.intro
  apply And.intro
  on_goal 2 => apply Eq.refl
  simp_all only

noncomputable
def iter {α : Type u} [CompleteLattice α] (lim : Set α -> α) (f : α -> α) (s : α)  (O : Ordinal.{u}) : α  :=
  let rec iter_helper o :=
    if o = 0 then s
    else
      let _ : Decidable (∃ x, x + 1 = o) := Classical.propDecidable (∃ x, x + 1 = o)
      if h: ∃ o', o' + 1 = o then
        let o' := Ordinal.pred o
        let _ : o' < o := by
          have : o' + 1 = o := by
            simp_all only [Ordinal.add_one_eq_succ]
            unhygienic with_reducible aesop_destruct_products
            aesop_subst h_1
            simp_all only [Ordinal.pred_succ]
          simp_all only [Ordinal.add_one_eq_succ, gt_iff_lt]
          unhygienic with_reducible aesop_destruct_products
          aesop_subst h_1
          simp_all only [Ordinal.add_one_eq_succ, Order.succ_eq_succ_iff, Order.lt_succ_iff_not_isMax, gt_iff_lt, not_isMax, not_false_eq_true]
        f (iter_helper o')
      else
        lim {if o' < o then iter_helper o' else s | o' < o}
  iter_helper O
termination_by iter_helper _ _ o => o

@[simp]
def iter_zero {α : Type u} [CompleteLattice α] (lim : Set α -> α) (f : α -> α) (s : α) : iter lim f s 0 = s := by
  unfold iter
  unfold iter.iter_helper
  simp

@[simp]
def iter_succ {α : Type u} [CompleteLattice α] (lim : Set α -> α) (f : α -> α) (s : α) (o : Ordinal) : iter lim f s (o + 1) = f (iter lim f s o) := by
  unfold iter
  conv => lhs; unfold iter.iter_helper
  have : ¬(o + 1 = 0) := by
    have := Ordinal.succ_ne_zero o
    have := Ordinal.add_one_eq_succ o
    simp_all only [ne_eq, Ordinal.add_one_eq_succ, not_false_eq_true]
  simp_all only [Ordinal.add_one_eq_succ, eq_iff_iff, iff_false, Order.succ_eq_succ_iff, exists_eq, Ordinal.pred_succ,
    Order.lt_succ_iff, dite_eq_ite, ite_true, ite_false]


@[simp]
def iter_lim {α : Type u} [CompleteLattice α] (lim : Set α -> α) (f : α -> α) (s : α) (o : Ordinal) :
    Ordinal.IsLimit o → iter lim f s o = lim {iter lim f s o' | o' < o} := by
  unfold Ordinal.IsLimit
  intro ⟨h1,h1'⟩
  have h2 : ¬∃ o', Order.succ o' = o := by
    intro h'
    apply Exists.elim h'
    intro o' _
    have h'' : o' < o := by aesop
    have : ¬(o' + 1 < o) := by aesop
    have := h1' o' h''
    contradiction
  have h3 x :
      (∃ o' < o, (if o' < o then iter.iter_helper lim f s o' else s) = x) =
        (∃ o' < o, iter.iter_helper lim f s o' = x) := by
        rename_i inst
        simp_all only [ne_eq, not_false_eq_true, true_and, not_exists, eq_iff_iff]
        apply Iff.intro
        · intro a
          unhygienic with_reducible aesop_destruct_products
          aesop_subst right
          simp_all only [ite_true]
          apply Exists.intro
          apply And.intro
          on_goal 2 => apply Eq.refl
          simp_all only
        · intro a
          unhygienic with_reducible aesop_destruct_products
          aesop_subst right
          apply Exists.intro
          split
          simp_all only [true_and]
          apply Eq.refl
          simp_all only
  unfold iter
  conv => lhs; unfold iter.iter_helper
  simp [h1,h2,h3]

-- def ordinal_induction (P : Ordinal -> Prop) (o : Ordinal):
--     P 0 -> (∀ o, P o -> P (o + 1)) -> (∀ o, Ordinal.IsLimit o -> (∀ o' < o, P o') -> P o) -> P o := by
--     exact fun a a_1 a_2 ↦ Ordinal.limitRecOn o a a_1 a_2

def iter_prefixes {α : Type u} [CompleteLattice α] (f : α -> α) (s : α) (o : Ordinal) (x : α) :
    Monotone f -> s ≤ x -> f x ≤ x -> iter sSup f s o ≤ x := by
    intro fmono
    intro sinc
    intro prefixx
    have : iter sSup f s 0 ≤ x := by
      unfold iter iter.iter_helper
      simp [sinc]
    have : ∀ o, iter sSup f s o ≤ x -> iter sSup f s (o + 1) ≤ x := by
      intro o
      intro h
      have : f (iter sSup f s o) ≤ f x := by
        simp_all [iter_succ]
        exact fmono h
      have : f (iter sSup f s o) ≤ x := Preorder.le_trans (f (iter sSup f s o)) (f x) x this prefixx
      have : f (iter sSup f s o) = iter sSup f s (o + 1) := by
        unfold iter
        conv => rhs; unfold iter.iter_helper
        have : o + 1 ≠ 0 := by
          intro
          have := Ordinal.succ_ne_zero o
          have : 1 ≠ 0 := by simp
          contradiction
        simp_all [h]
      simp_all only [iter_zero, Ordinal.add_one_eq_succ]
    have : ∀ o, Ordinal.IsLimit o -> (∀ o' < o, iter sSup f s o' ≤ x) -> iter sSup f s o ≤ x := by
      intro o
      intro hlim
      intro hless
      have : ∀ x' ∈ {iter sSup f s o' | o' < o}, x' ≤ x := by
        intro x'
        intro hx
        have : ∃ o' < o, x' = iter sSup f s o' := by
          simp_all only [iter_zero, Ordinal.add_one_eq_succ, Set.mem_setOf_eq]
          unhygienic with_reducible aesop_destruct_products
          aesop_subst right
          apply Exists.intro
          apply And.intro
          on_goal 2 => apply Eq.refl
          simp_all only
        apply Exists.elim this
        intro o'
        intro hxo'
        rw [And.right hxo']
        exact hless o' (And.left hxo')
      have : sSup {iter sSup f s o' | o' < o} ≤ x := by
        simp_all only [Set.mem_setOf_eq, iter_zero, Ordinal.add_one_eq_succ, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, implies_true, forall_const, sSup_le_iff]
      have : iter sSup f s o = sSup {iter sSup f s o' | o' < o} := by simp [hlim]
      rw [this]
      assumption
    have := Ordinal.limitRecOn (C := (fun o : Ordinal => iter sSup f s o ≤ x))
    simp_all only [iter_zero, Ordinal.add_one_eq_succ, iter_lim, sSup_le_iff, Set.mem_setOf_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, implies_true, forall_const, forall_true_left]

def iter_monotone_chain {α : Type u} [CompleteLattice α] (f : α -> α) (s : α) (o1 : Ordinal) (o2 : Ordinal) :
    Monotone f -> s ≤ f s -> o1 ≤ o2 -> iter sSup f s o1 ≤ iter sSup f s o2 := by sorry

noncomputable
def bigord {α : Type u} [CompleteLattice α] : Ordinal := Cardinal.ord (Cardinal.mk (Set α))

def iter_reach_fixpoint {α : Type u} [CompleteLattice α] (f : α -> α) (h : Monotone f) (s : α) :
    s ≤ f s -> iter sSup f s (bigord (α := α)) = f (iter sSup f s (bigord (α := α))) := by
  intro hs
  apply Classical.byContradiction
  intro hbigord
  have : ∀ o ≤ bigord (α := α), ∀ o' < o, iter sSup f s o' < iter sSup f s o := by sorry
  sorry

noncomputable
def iter_lfp {α : Type u} [CompleteLattice α] (f : α -> α) (h : Monotone f) : α :=
  iter sSup f Bot.bot (bigord (α := α))

def iter_lfp_fixed {α : Type u} [CompleteLattice α] (f : α -> α) (h : Monotone f) :
  f (iter_lfp f h) = iter_lfp f h := by sorry

def iter_lfp_least {α : Type u} [CompleteLattice α] (f : α -> α) (h : Monotone f) (x : α) :
  f x = x -> iter_lfp f h ≤ x := by sorry
