-- This module serves as the root of the `ToT` library.
-- Import modules here that should be built as part of the library.
import «ToT».Basic
import Lean

structure ToTType where
  F : Nat → Type
  restr : (n : Nat) → F (n + 1) → F n

def ToTType.restrmaphelp (n : Nat) : (k : Nat) → F A (n + k) → F A n
  | 0, a => a
  | h+1 , a => restrmaphelp n h (A.restr (n+h) a)

def LThelp (n m : Nat) (h : m ≤ n) : {k : Nat // m+k = n} where
  val := n-m
  property := by
--     omega
     exact Nat.add_sub_of_le h
     -- Found using apply?
     -- by omega tactic

def ToTType.testr (n m : Nat) (p : n=m) (a : F A n) : F A m
  := p ▸ a
  -- let q : F A n = F A m := by rw[p];
  -- cast q a

def ToTType.restrmap (n m : Nat) (h : m ≤ n) (a : F A n) : F A m
  := let ⟨ n_minus_m, p⟩ := LThelp n m h;
     let q : F A n = F A (m + n_minus_m) := by rw[p];
     restrmaphelp m n_minus_m (cast q a)

def ToTHom (A B : ToTType) : Type
    := {f : (n : Nat) → A.F (n) → B.F (n) // (∀n x, B.restr n (f (n+1) x) = f n (A.restr n x))}

instance : Coe Type ToTType where
  coe T := { F := fun _ => T, restr := fun _ => id}

infixr:60 " ⤳ " => ToTHom

def ToTType.delta {A B : Type} (f : A → B) : A ⤳ B where
  val := fun _ => f
  property := by
      intro n
      intro x
      rfl

def ToTType.const {A : ToTType} {B : Type} (b : B) : A ⤳ B where
  val := fun n _ => b
  property := by
    intro n
    intro x
    rfl

def ToTType.id (A : ToTType) : A ⤳ A where
  val :=  fun _ x => x
  property :=  by
    intro n
    intro y
    rfl

def ToTType.comp (f : A ⤳ B) (g : B ⤳ C) : A ⤳ C where
  val := fun n => g.val n ∘ f.val n
  property := by
    intro n x
    let ⟨ fval, fprop⟩ := f
    let ⟨ gval, gprop⟩ := g
    simp
    rw [← fprop, ← gprop]

-- Associativity, lid and rid, later, fixpoints, streams, guarded recursive types

def ToTType.Later (A : ToTType) : ToTType where
  F := fun
        | 0 => Unit
        | n+1 => A.F n
  restr := fun
        | 0, _ => ()
        | n+1, x => A.restr n x

notation:70 "▷" T => ToTType.Later T

def ToTType.Earlier (A : ToTType) : ToTType where
  F := fun n => A.F (n+1)
  restr := fun n => A.restr (n+1)

notation:70 "◁" T => ToTType.Earlier T

def ToTType.delayF (f : (◁ A) ⤳ B) : (n : Nat) → A.F n → (▷B).F n
 | 0 , a => ()
 | n+1 , a => f.val n a

def ToTType.delay (f : (◁ A) ⤳ B) : A ⤳ ▷B where
  val := delayF f
  property := by
      intro n
      cases n with
      | zero =>
        simp [delayF]
        intro x
        cases (▷B).restr 0 (f.val 0 x)
        rfl
      | succ n =>
        simp [delayF]
        exact f.property n

def ToTType.adv (f : A ⤳ ▷B) : (◁A) ⤳ B where
  val := fun n => f.val (n+1)
  property := fun n => f.property (n+1)


def ToTType.Prod (A B : ToTType) : ToTType where
  F := fun n => (A.F n)× (B.F n)
  restr := fun n x => (A.restr n (Prod.fst x), B.restr n (Prod.snd x))

def ToTType.fst (A B : ToTType) : (ToTType.Prod A B) ⤳ A where
  val := fun n => Prod.fst
  property := by
               intro n
               intro x
               rfl


def ToTType.snd (A B : ToTType) : (ToTType.Prod A B) ⤳ B where
  val := fun n => Prod.snd
  property := by
               intro n
               intro x
               rfl

def ToTType.pair (A B C : ToTType) (f : C ⤳ A) (g : C ⤳ B) : (C ⤳ ToTType.Prod A B) where
  val := fun n c => (f.val n c, g.val n c)
  property := by
               intro n
               intro x
               simp [ToTType.restr,Prod]
               constructor
               case left => exact f.property n x
               case right => exact g.property n x


def ToTType.cutF (A : ToTType) (n : Nat) : Nat → Type :=
  fun m => PProd (m ≤ n) (A.F m)

def ToTType.cut (A : ToTType) (n : Nat) : ToTType where
  F := cutF A n
  restr := fun m =>
    if h : m+1 ≤ n then
      fun ⟨_, y⟩ => ⟨by exact Nat.le_of_succ_le h, A.restr m y⟩
    else by
      intro a
      simp [cutF] at a
      cases a
      contradiction

def ToTType.cutRestr {A : ToTType} {n : Nat} : (cut A n)⤳(cut A (n+1)) where
  val := fun m => if h : m ≤ n then
    fun ⟨_, y⟩ => ⟨by omega, y⟩
    else by
      intro h
      simp [cut] at h
      simp [cutF] at h
      cases h
      contradiction
  property := by
    intro p
    intro x
    simp
    split
    . split
      . simp
        cases x
        have : p+1≤ n+1 := by omega
        simp [cut, *]
      . omega
    . cases x
      contradiction


def ToTType.Fun (A B : ToTType) : ToTType where
  F := fun n => cut A n ⤳ B
  restr := fun _ h => comp cutRestr h

def ToTType.ev (A B : ToTType) : Prod (Fun A B) A ⤳ B where
  val := fun n => fun fa =>
    let a := (Prod.snd fa)
    let f := (Prod.fst fa).val n
    f ⟨by simp , a⟩
  property := by
    intro n
    intro x
    cases x
    simp[Prod, Fun,comp,cutRestr]
    sorry

def ToTType.lamF (f : Prod A B ⤳ C) (n : Nat) (a : F A n) : cut B n ⤳ C where
  val := fun m b =>
    if h : m ≤ n then
      let bval : F B m := b.snd
      let a_restr : F A m := restrmap n m h a
      f.val m (a_restr, bval)
    else
      let e : False := h (b.fst)
      by contradiction
  property := by
      intro m x
      simp
      by_cases h : (m+1 ≤ n)-- why can I not write with h
      sorry
      sorry


def ToTType.lam (f : Prod A B ⤳ C) : A ⤳ Fun B C where
 val := lamF f
 property := by
   intro n x
   funext
   sorry

def fixpoint (A : ToTType) (f : (▷A) ⤳ A) : (Unit ⤳ A) where
  val := let rec go
          | 0 => f.val 0
          | n+1 => f.val (n+1) ∘ (go n)
          go
  property := by
               intro n x
               sorry

def fixpval {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A): (n : Nat) →  Γ.F n → A.F n
  | 0, γ => f.val 0 (γ, ())
  | n+1, γ => f.val (n+1) (γ, fixpval f n (Γ.restr n γ))

def fixp {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A) : Γ ⤳ A where
  val := fixpval f
  property := by sorry

def ToTType.Str.go (A : Type) : Nat → Type
  | 0 => A
  | n + 1 => A × go A n


def ToTType.Str (A : Type) : ToTType where
  F := ToTType.Str.go A
  restr := fun _ => Prod.snd

--def ToTType.Str.tailmap (A : Type) (xs : ToTType.Str A) : (n : Nat) →

def ToTType.Str.tail {A : Type} : ToTType.Str A ⤳ ▷(ToTType.Str A) where
     val := (▷(ToTType.Str A)).restr
     property := by
                  sorry

def ToTType.Str.head {A : Type} : ToTType.Str A ⤳ A where
     val := let rec go
      | 0 => fun x => x
      | n + 1 => Prod.fst
      go
     property := by
                  sorry

def ToTType.Str.cons {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) : Γ ⤳ (ToTType.Str B) where
  val := let rec go
    | 0 => g.val 0
    | n + 1 => fun γ => (g.val _ γ, f.val _ γ)
    go
  property := by
     sorry

def zeros : Unit ⤳ ToTType.Str Nat := fixpoint (ToTType.Str Nat) (ToTType.Str.cons (ToTType.const 0) (ToTType.id _))

--- zeros : ToTType.Str Nat := fix x. 0 :: x
--- cons (a : A) (xs : Str A) := fold (a, xs)

declare_syntax_cat ToTExpr
syntax "[" term "]" : ToTExpr
syntax "fix" "(" ident ":" term ")" "=>" ToTExpr : ToTExpr
syntax ident : ToTExpr
syntax ToTExpr "::" ToTExpr : ToTExpr
syntax "box(" ToTExpr ")" : term

open Lean Elab Term
partial def elabToTExpr (stx : TSyntax `ToTExpr ) : TermElabM (TSyntax `term) :=
  match stx with
  | `(ToTExpr|[$t]) => `(ToTType.const $t)
  | `(ToTExpr|fix ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr body
    `(fixpoint $A $bodyExpr)
  | `(ToTExpr|$x:ident) => `(ToTType.id _)
  | `(ToTExpr|$h :: $t) => do
    let hd <- elabToTExpr h
    let tl <- elabToTExpr t
    `(ToTType.Str.cons $hd $tl)
  | _ => throwErrorAt stx "Did not understand"

elab_rules : term
  | `( box($t) ) => do
    let f <- elabToTExpr t
    elabTerm f none

#eval (box([4+3]) : Unit ⤳ Nat).val 0 ()

def pretty_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::tl)



def Box (A : ToTType) : Type := Unit ⤳ A

abbrev Scream (A : Type) := Box (ToTType.Str A)

def force {A : ToTType} (b : Box (▷A)) : Box A where
  val := fun n => b.val (n+1)
  property := by sorry

def ToTType.Str.cihead {A : Type} (s : Scream A) : A := s.val 0 ()

def ToTType.Str.citail {A : Type} (s : Scream A) : Scream A := force (ToTType.comp s ToTType.Str.tail)

def ToTType.Str.take (s : Scream A) : Nat → List A
  | 0 => []
  | n+1 => cihead s :: take (citail s) n

#eval ToTType.Str.take zeros 8
#eval ToTType.Str.take pretty_zeros 8

def ToTType.Str.map {A B : Type} (f : A → B) : (ToTType.Str A) ⤳ (ToTType.Str B) :=
  fixp (cons )

#check Nat ⤳ Nat
