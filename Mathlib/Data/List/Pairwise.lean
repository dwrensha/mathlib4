/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# Pairwise relations on a List
This file provides basic results about `List.pairwise` and `List.pwFilter` (definitions are in
`data.List.defs`).
`Pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the List obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the List we have so far. It thus yields `l'` a maximal subList of `l` such that
`Pairwise r l'`.
## Tags
sorted, nodup
-/

open Nat Function

namespace List

variable {α : Type _} {R : α → α → Prop} {a : α} {l : List α}

/-! ### Pairwise -/

lemma rel_of_pairwise_cons (p : (a :: l).Pairwise R) : ∀ {a'}, a' ∈ l → R a a' :=
  λ {a'} => (Pairwise_cons.1 p).1 a'

lemma Pairwise.of_cons (p : (a :: l).Pairwise R) : Pairwise R l := (Pairwise_cons.1 p).2

theorem Pairwise.tail : ∀ {l : List α} (p : Pairwise R l), Pairwise R l.tail
| [], h => h
| _ :: _, h => h.of_cons

theorem Pairwise.drop : ∀ {l : List α} {n : ℕ}, Pairwise R l → Pairwise R (l.drop n)
| _, 0, h => h
| [], _ + 1, _ => Pairwise.nil
| _ :: l, n + 1, h => @Pairwise.drop l n (Pairwise_cons.mp h).right

theorem Pairwise.imp_of_mem {S : α → α → Prop} {l : List α}
  (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b) (p : Pairwise R l) : Pairwise S l :=
by induction p with
   | nil => constructor
   | cons a' _ IH =>
          constructor
          · exact ball.imp_right
              (λ x h => H (mem_cons_self _ _) (mem_cons_of_mem _ h)) a'
          · exact IH (λ {a b} m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m'))

lemma Pairwise.imp (H : ∀ a b, R a b → S a b) : Pairwise R l → Pairwise S l :=
Pairwise.imp_of_mem (λ {a b} _ _ => H a b)

lemma pairwise_and_iff : l.Pairwise (λ a b => R a b ∧ S a b) ↔ l.Pairwise R ∧ l.Pairwise S :=
⟨λ h => ⟨h.imp (λ a b h => h.1), h.imp (λ a b h => h.2)⟩,
 λ pair =>
  by let ⟨hR, hS⟩ := pair
     clear pair -- TODO mathlib3 does this more cleanly with clear_
     induction hR with
     | nil => simp only [Pairwise.nil, Pairwise_cons]
     | cons R1 _ IH =>
           simp only [Pairwise.nil, Pairwise_cons] at *
           exact ⟨λ b bl => ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩⟩

lemma Pairwise.and (hR : l.Pairwise R) (hS : l.Pairwise S) :
  l.Pairwise (λ a b => R a b ∧ S a b) :=
pairwise_and_iff.2 ⟨hR, hS⟩

lemma Pairwise.imp₂ (H : ∀ a b, R a b → S a b → T a b) (hR : l.Pairwise R) (hS : l.Pairwise S) :
  l.Pairwise T :=
(hR.and hS).imp $ λ a b => And.rec (H a b)

theorem Pairwise.iff_of_mem {S : α → α → Prop} {l : List α}
  (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : Pairwise R l ↔ Pairwise S l :=
⟨Pairwise.imp_of_mem (λ m m' => (H m m').1),
 Pairwise.imp_of_mem (λ m m' => (H m m').2)⟩

theorem Pairwise.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {l : List α} : Pairwise R l ↔ Pairwise S l :=
Pairwise.iff_of_mem (λ {a b} _ _ => H a b)

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwise R l :=
by induction l with
   | nil => exact Pairwise.nil
   | cons a' l' ih =>
       simp only [*, Pairwise_cons, forall_2_true_iff]

theorem Pairwise.and_mem {l : List α} :
  Pairwise R l ↔ Pairwise (λ x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
Pairwise.iff_of_mem
  (by simp (config := {contextual := true}) only [true_and, iff_self, implies_true])

theorem Pairwise.imp_mem {l : List α} :
  Pairwise R l ↔ Pairwise (λ x y => x ∈ l → y ∈ l → R x y) l :=
Pairwise.iff_of_mem
  (by simp (config := {contextual := true}) [forall_prop_of_true, iff_self, forall_2_true_iff])

--protected lemma pairwise.sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → Pairwise R l₂ → Pairwise R l₁
--| ._, ._, Sublist.slnil h => h
--| ._ ._ (sublist.cons l₁ l₂ a s) (pairwise.cons i h) => h.sublist s
--| ._ ._ (sublist.cons2 l₁ l₂ a s) (pairwise.cons i h) =>
--  (h.sublist s).cons (ball.imp_left s.subset i)

lemma Pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : l.Pairwise R)
  (h₃ : l.Pairwise (flip R)) :
  ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y := by
  induction l with
  | nil => exact forall_mem_nil _
  | cons a l ih =>
    rw [Pairwise_cons] at h₂ h₃
    rintro x (_ | ⟨_, _, _, hx⟩) y (_ | ⟨_, _, _, hy⟩)
    · exact h₁ _ (l.mem_cons_self _)
    · exact h₂.1 _ hy
    · exact h₃.1 _ hx
    · exact ih (λ x hx => h₁ _ $ mem_cons_of_mem _ hx) h₂.2 h₃.2 hx hy

--lemma Pairwise.forall_of_forall (H : symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
--  ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
--H₂.forall_of_forall_of_flip H₁ $ by rwa H.flip_eq

-- TODO Pairwise.forall, Pairwise.set_pairwise

theorem Pairwise_singleton (R) (a : α) : Pairwise R [a] :=
by simp [Pairwise_cons, Pairwise.nil]

theorem Pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b :=
by simp [Pairwise_cons, Pairwise.nil]

-- TODO in mathlib3 this is:
--by simp only [pairwise_cons, mem_singleton, forall_eq, forall_prop_of_false (not_mem_nil _),
--  forall_true_iff, pairwise.nil, and_true]

variable [DecidableRel R]

@[simp] theorem pwFilter_nil : pwFilter R [] = [] := rfl

@[simp] theorem pwFilter_cons_of_pos {a : α} {l : List α} (h : ∀ b ∈ pwFilter R l, R a b) :
  pwFilter R (a :: l) = a :: pwFilter R l := if_pos h

@[simp] theorem pwFilter_cons_of_neg {a : α} {l : List α} (h : ¬ ∀ b ∈ pwFilter R l, R a b) :
  pwFilter R (a :: l) = pwFilter R l := if_neg h

theorem pwFilter_subset {l : List α} : ∀ (a : α), a ∈ pwFilter R l → a ∈ l := by
  intro a ha
  induction l with
  | nil => rwa [pwFilter_nil] at ha
  | cons x l ih => sorry

theorem pairwise_pwFilter : ∀ (l : List α), Pairwise R (pwFilter R l)
| []     => Pairwise.nil
| x :: l => by
  by_cases (∀ y ∈ pwFilter R l, R x y)
  · rw [pwFilter_cons_of_pos h]
    exact Pairwise_cons.2 ⟨h, pairwise_pwFilter l⟩
  · rw [pwFilter_cons_of_neg h]
    exact pairwise_pwFilter l

theorem pwFilter_eq_self {l : List α} : pwFilter R l = l ↔ Pairwise R l := by
  constructor
  · exact λ e => e ▸ pairwise_pwFilter l
  · intro p
    induction l with
    | nil => rfl
    | cons x l ih =>
      have ⟨ha, hl⟩ := Pairwise_cons.1 p
      conv => rhs; rw [← ih hl]
      exact pwFilter_cons_of_pos λ b hb => ha b (pwFilter_subset b hb)

@[reducible] theorem Pairwise.pwFilter : Pairwise R l → pwFilter R l = l :=
  pwFilter_eq_self.2
