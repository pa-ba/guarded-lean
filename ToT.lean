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

def ToTType.restrmap (h : m ≤ n) (a : F A n) : F A m
  := let ⟨ n_minus_m, p⟩ := LThelp n m h;
     let q : F A n = F A (m + n_minus_m) := by rw[p];
     restrmaphelp m n_minus_m (cast q a)

def ToTType.restrmapEq (p : m+1 ≤ n) (a : F A n) : A.restr m (restrmap p a) = restrmap (by omega) a
 := let k := n-(m+1)
     by
      induction k with
      | zero => have q : n = (m+1) := by sorry
                have r : (LThelp n (m+1) p).val = 0 := by sorry
                simp[restrmap,restrmaphelp,r]
                sorry
      | succ m p => sorry


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

def ToTType.id : A ⤳ A where
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
 | 0 , _ => ()
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

def ToTType.next : A ⤳ ▷A where
  val
   | 0, _ => ()
   | n+1, a => A.restr n a
  property := by
               intro n x
               simp
               induction n with
               | zero => simp[Later]
               | succ m _ => simp[Later]

def ToTType.Prod (A B : ToTType) : ToTType where
  F := fun n => (A.F n)× (B.F n)
  restr := fun n x => (A.restr n (Prod.fst x), B.restr n (Prod.snd x))

def ToTType.fst : (ToTType.Prod A B) ⤳ A where
  val := fun n => Prod.fst
  property := by
               intro n
               intro x
               rfl


def ToTType.snd : (ToTType.Prod A B) ⤳ B where
  val := fun n => Prod.snd
  property := by
               intro n
               intro x
               rfl

--def ToTType.pair (A B C : ToTType) (f : C ⤳ A) (g : C ⤳ B) : (C ⤳ ToTType.Prod A B) where
def ToTType.pair (f : C ⤳ A) (g : C ⤳ B) : (C ⤳ ToTType.Prod A B) where
  val := fun n c => (f.val n c, g.val n c)
  property := by
               intro n
               intro x
               simp [ToTType.restr,Prod]
               constructor
               case left => exact f.property n x
               case right => exact g.property n x

def ToTType.unitFinal : A ⤳ Unit where
  val := fun _ _ => ()
  property := by
               intro n _
               simp


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

def ToTType.ev : Prod (Fun A B) A ⤳ B where
  val := fun n => fun fa =>
    let a := (Prod.snd fa)
    let f := (Prod.fst fa).val n
    f ⟨by simp , a⟩
  property := by
    intro n
    intro x
    have xfun := x.fst
    have xa := x.snd
    have q : x = (xfun,xa) := by sorry
    simp[Prod, Fun,comp,cutRestr]
    let r := xfun.property n _ --(by sorry, xa)
    apply?
    sorry

def ToTType.lamF (f : Prod A B ⤳ C) (n : Nat) (a : F A n) : cut B n ⤳ C where
  val := fun m b =>
    if h : m ≤ n then
      let bval : F B m := b.snd
      let a_restr : F A m := restrmap h a
      f.val m (a_restr, bval)
    else
      let e : False := h (b.fst)
      by contradiction
  property := by -- what is unsolved here?
      intro m x
      simp
      by_cases h : (m+1 ≤ n)
      have k : m ≤ n := by omega
      simp[h,k]
      -- apply f.property m (restrmap h a,x.snd)
--      simp[restrmap n (m+1) h a]
      --exact f.property m (restrmap h a,x.snd)
      sorry
      simp[h]
      by_cases k : (m ≤ n)
      simp[k]
      have p : (m=m) := by omega


def ToTType.lam (f : Prod A B ⤳ C) : A ⤳ Fun B C where
 val := lamF f
 property := by
   intro n x
   simp[lamF]
   -- funext
   apply?
   sorry

def ToTType.funcomp : Prod (Fun A B) (Fun B C) ⤳ Fun A C
  := let firststep : Prod (Prod (Fun A B) (Fun B C)) A ⤳ B
       := comp (pair (comp fst fst) snd) ev;
     let resultcurr : Prod (Prod (Fun A B) (Fun B C)) A ⤳ C
       := comp (pair (comp fst snd) firststep) ev;
     lam resultcurr


def ToTType.appfun : Prod (▷(Fun A B)) (▷A) ⤳ ▷B
 := let f : (◁(Prod (▷(Fun A B)) (▷A))) ⤳ Fun A B
          := adv fst;
    let x : (◁(Prod (▷(Fun A B)) (▷A))) ⤳ A
          := adv snd;
    let fx : (◁(Prod (▷(Fun A B)) (▷A))) ⤳ B := (comp (pair f x) ev);
    ToTType.delay fx


def fixpval {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A): (n : Nat) →  Γ.F n → A.F n
  | 0, γ => f.val 0 (γ, ())
  | n+1, γ => f.val (n+1) (γ, fixpval f n (Γ.restr n γ))

def fixprop {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A) : (n : Nat) →  (γ : Γ.F (n+1)) → fixpval f (n+1) γ = f.val (n+1) (γ, fixpval f n (Γ.restr n γ))
  | 0, γ => by
             simp[fixpval]
  | n+1, γ => by
               simp[fixpval]

def fixp {Γ A : ToTType} (f : ToTType.Prod Γ (▷A) ⤳ A) : Γ ⤳ A where
  val := fixpval f
  property := by
    intro n γ
    induction n with
    | zero => simp[fixpval]
              apply f.property
    | succ m p => simp[fixpval,f.property,ToTType.Prod,Later,p]
                  simp[fixprop f m (Γ.restr (m+1) γ)]
-- What is the problem with Later here? ToTType.Later does not help

def fixpoint (A : ToTType) (f : (▷A) ⤳ A) : (Unit ⤳ A)
  := let g : ToTType.Prod Unit (▷A) ⤳ A := ToTType.comp (ToTType.snd Unit (▷A)) f;
     fixp g

-- Show fixpoint is fixed point

def ToTType.StrF (A : Type) : Nat → Type
  | 0 => A × Unit
  | n + 1 => A × StrF A n

def ToTType.StrR (A : Type) : (n : Nat) → StrF A (n+1) → StrF A n
   | 0, (a, _) => (a, ())
   | n+1, (a, as) => (a, StrR A n as)

def ToTType.Str (A : Type) : ToTType where
  F := ToTType.StrF A
  restr := StrR A

--def ToTType.Str.tailmap (A : Type) (xs : ToTType.Str A) : (n : Nat) →

def ToTType.StrUnfold (A : Type) (n : Nat) : (ToTType.Str A).F n = (A × (▷(ToTType.Str A)).F n)
 := by
      simp[Str,Later]
      cases n
      simp
      rfl
      simp[StrF]

def ToTType.Str.tail {A : Type} : ToTType.Str A ⤳ ▷(ToTType.Str A) where
     val
      | 0, a => a.snd
      | n+1, a => a.snd
     property := by
                  intro n x
                  simp[Later]
                  cases n
                  simp
                  constructor


def ToTType.Str.headmap {A : Type} : (n : Nat) →  (as : (Str A).F n) →  A
  := fun n a => ((StrUnfold A n) ▸ a).fst

def ToTType.Str.head {A : Type} : ToTType.Str A ⤳ A where
     val := headmap
     property := by
                  intro n
                  intro x
                  simp[headmap, Str, StrR]
                  induction n with
                  | zero => simp[StrR]
                  | succ m _ => simp[Later,StrR]

def ToTType.Str.consmap {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) (n : Nat) : Γ.F n → (ToTType.Str B).F n
  := fun γ => StrUnfold B n ▸ (g.val n γ, f.val n γ)

def ToTType.Str.cons {Γ : ToTType} {B : Type} (g : Γ ⤳ B) (f : Γ ⤳ ▷(ToTType.Str B)) : Γ ⤳ (ToTType.Str B) where
  val := consmap g f
  property := by
     intro n x
     simp[consmap,Str]
     induction n with
     | zero => simp[StrR]
               apply congr
               apply congr
               rfl
               exact g.property 0 x
               constructor
     | succ m _ => simp[StrR]
                   apply congr
                   apply congr
                   rfl
                   exact g.property (m+1) x
                   exact f.property (m+1) x

def zeros : Unit ⤳ ToTType.Str Nat := fixpoint (ToTType.Str Nat) (ToTType.Str.cons (ToTType.const 0) (ToTType.id))

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
  property := by
               intro n x
               simp
               exact b.property (n+1) x

def ToTType.Str.cihead {A : Type} (s : Scream A) : A := (s.val 0 ()).fst

def ToTType.Str.citail {A : Type} (s : Scream A) : Scream A := force (ToTType.comp s ToTType.Str.tail)

def ToTType.Str.take (s : Scream A) : Nat → List A
  | 0 => []
  | n+1 => cihead s :: Str.take (citail s) n

def ToTType.Str.map {A B : Type} (f : A → B) : (Str A) ⤳ (Str B) :=
  let appf : (Str A) ⤳ B
    := comp head (delta f);
  let hdout : (ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A)) ⤳ B
    := comp snd appf;
  let dgrass : (ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A)) ⤳ ▷(Fun (Str A) (Str B))
    := ToTType.fst;
  let grass : (◁(ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A))) ⤳ (Fun (Str A) (Str B))
    := adv (dgrass); -- GR assumption, grass
  let tl : ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A) ⤳ ▷(Str A)
    := comp snd tail;
  let delaytl : (◁(ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A))) ⤳ Str A
    := adv (tl);
  let tlout : ToTType.Prod (▷(Fun (Str A) (Str B))) (Str A) ⤳ ▷(Str B)
    := delay (comp (pair grass delaytl) ev)
  let fpterm : (▷(Fun (Str A) (Str B))) ⤳ Fun (Str A) (Str B)
    := lam (cons hdout tlout);
  let resultcurr : Unit ⤳ Fun (Str A) (Str B)
    := fixpoint (Fun (Str A) (Str B)) fpterm;
  let resultuncurr : Prod Unit (Str A) ⤳ Str B
    := comp (pair (comp fst resultcurr) snd) ev;
  comp (pair unitFinal ToTType.id) resultuncurr

def ToTType.Str.from : Nat ⤳ (Str Nat) :=
   let hdout : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Nat
     := snd
   let succsnd : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Nat
     := comp snd (delta (fun n => n+1))
   let tlout : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ ▷ (Str Nat)
     := comp (pair fst (comp succsnd next)) appfun
   let fpfuncurr : Prod (▷(Fun Nat (Str Nat))) Nat ⤳ Str Nat
     := cons hdout tlout
   let fpfun : (▷(Fun Nat (Str Nat))) ⤳ Fun Nat (Str Nat)
     := lam fpfuncurr
   let almostresult : Nat ⤳ Fun Nat (Str Nat)
     := fixp (comp snd fpfun)
   comp (pair almostresult id) ev

def ToTType.Str.natseq : Box (Str Nat) := comp (delta (fun _ => 0)) Str.from

#eval ToTType.Str.take (ToTType.Str.natseq) 8

--#eval ToTType.Str.take zeros 8
--#eval ToTType.Str.take pretty_zeros 8

--#check Nat ⤳ Nat
