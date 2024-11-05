-- This module serves as the root of the `ToT` library.
-- Import modules here that should be built as part of the library.
import Lean

structure ToTType where
  F : Nat → Type
  restr : (n : Nat) → F (n + 1) → F n

def ToTType.cast {A : ToTType} (p : n = k) : A.F n → A.F k := (p ▸ ·)

@[simp]
theorem ToTType.cast_refl_id {A : ToTType} {p : n = n} {x : A.F n} : A.cast p x = x := by
  cases p
  rfl

@[simp]
theorem ToTType.cast_cast_trans {A : ToTType} {p : n = k} {q : k = j} {x : A.F n} : A.cast q (A.cast p x) = A.cast (p.trans q) x := by
  cases p
  rfl

theorem Subtype.valEq : x = w -> Subtype.mk x y = Subtype.mk w z :=
  by
   intro h
   cases h
   rfl

def ToTType.restrmaphelp (n : Nat) : (k : Nat) → F A (n + k) → F A n
  | 0, a => a
  | h+1 , a =>
    let p : (n + (h + 1)) = (n + 1 + h) := by omega
    A.restr n (restrmaphelp (n+1) h (A.cast p a))
--  | h+1 , a => restrmaphelp n h (A.restr (n+h) a)

def restrmaphelpzero
    (n k : Nat)
    (p : k = 0) (q : n + k = n)
    (x : ToTType.F A (n+k))
    : ToTType.restrmaphelp n k x = A.cast q x := by
  cases p
  simp [ToTType.restrmaphelp]

def restrmaphelpsucc (n k : Nat)
    (p : k = k'+ 1)
    (q : n + k = n + 1 + k')
    (x : ToTType.F A (n+k))
    : ToTType.restrmaphelp n k x = A.restr n (ToTType.restrmaphelp (n+1) k' (A.cast q x)) := by
  cases p
  simp [ToTType.restrmaphelp]

def LThelp (n m : Nat) (h : m ≤ n) : {k : Nat // m+k = n} where
  val := n-m
  property := by
--     omega
     exact Nat.add_sub_of_le h
     -- Found using apply?
     -- by omega tactic

@[simp]
def LThelpZero (m n : Nat) (p : m+1=n) (q : m+1 ≤ n) : (LThelp n (m+1) q).val = 0
  := by
      have : n-(m+1) = 0 := by omega
      unfold LThelp
      simp[this]

@[simp]
def LThelpVal (m n : Nat) (p : m ≤ n) : (LThelp n m p).val = n - m
  := by
      unfold LThelp
      simp

def ToTType.testr (n m : Nat) (p : n=m) (a : F A n) : F A m
  := p ▸ a
  -- let q : F A n = F A m := by rw[p];
  -- cast q a

def ToTType.restrmap (h : m ≤ n) (a : F A n) : F A m
  := let ⟨ n_minus_m, p⟩ := LThelp n m h;
     let q : n = (m + n_minus_m) := by rw[p];
     restrmaphelp m n_minus_m (A.cast q a)


set_option pp.proofs.withType true

def ToTType.restrmapEq
    (p : m+1 ≤ n)
    (q : m ≤ n)
    (a : F A n)
    : A.restr m (restrmap p a) = restrmap q a := by
  let d := LThelp n (m+1) p
  let ⟨ k, klt⟩ := d
  induction k with
  | zero =>
    simp only [restrmap]
    rw [restrmaphelpzero] <;> try (simp_arith; omega)
    rw [restrmaphelpsucc (k':=0)] <;> try (simp_arith; omega)
    rw [restrmaphelpzero] <;> try rfl
    simp
  | succ k' =>
    simp only [restrmap]
    -- conv => lhs ; unfold restrmaphelp
    have : (LThelp n (m + 1) p).val = k'+ 1 := by
      simp; omega
    apply Eq.symm
    have := restrmaphelpsucc (A := A) (n := m) (k := (LThelp n m q).val) (k' := (LThelp n (m + 1) p).val) (p := by simp; omega) (q := by simp; omega) <| by
      simp
      apply cast ?prf
      . exact a
      . omega
    simp at this
    apply this

def ToTType.restrmaphelpEqInnerZero
  (m n : Nat)
  (A : ToTType)
  (p : m ≤ n + 1)
  (q : m ≤ n)
  (a : A.F (n + 1))
  (klt : m + 0 = n)
  : restrmap p a = restrmap q (A.restr n a) := by
    simp at klt
    cases klt
    simp[restrmap]
    have := restrmaphelpzero (A := A) m (LThelp m m q).val ?e (by simp)
    rw[this]
    simp
    have := restrmaphelpsucc (k':=0) m (A := A) 1 rfl rfl a
    rw[restrmaphelpsucc (k':=0)] <;> try (simp_arith; omega)
    rw[restrmaphelpzero ] <;> try (simp_arith; omega)
    case q => rfl
    all_goals (try simp[LThelp])
    case q => omega
    simp

def ToTType.restrmapEqInner
    (p : m ≤ n+1)
    (q : m ≤ n)
    (a : F A (n+1))
    : restrmap p a = restrmap q (A.restr n a) := by
      unfold restrmap
      cases LThelp n m q with | mk k klt =>
      cases LThelp (n+1) m p with | mk k'' klt' =>
      /-simp[restrmap]
      cases LThelp n m q with | mk k klt =>
      cases LThelp (n+1) m p with | mk k' klt' =>
      dsimp-/
      dsimp
      induction k generalizing m with
      | zero =>
        -- simp[restrmap]
        sorry
--        simp at klt
--        cases klt
--        simp[LThelp]
--        have : m-m = 0 := by simp_arith
/-
type mismatch
  PLaterProp
has type
  (◁?m.78805).ToTPred → {n : Nat} → ?m.78805.F n → Prop : Type
but is expected to have type
  Γ.F n✝ → Prop : Type
the following variables have been introduced by the implicit lambda feature
  n✝ : Nat
you can disable implicit lambdas using `@` or writing a lambda expression with `{}` or `[]` binder annotations.
-/
--        apply restrmaphelpEqInnerZero <;> omega
      | succ k' IH =>
        dsimp[restrmaphelp]
        have : k'' = k'+2 := by omega
        subst this
        dsimp[restrmaphelp]
        apply congrArg
        have := IH (m := m+1) (by omega) (by omega) (by omega)
        simp_all
        sorry


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

def ToTType.prev : (◁Γ) ⤳ Γ := adv (next)

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

def ToTType.ProdHom (f : A ⤳ C) (g : B ⤳ D) : (Prod A B) ⤳ (Prod C D) :=
  pair (comp fst f) (comp snd g)

def ToTType.unitFinal : A ⤳ Unit where
  val := fun _ _ => ()
  property := by
               intro n _
               simp


def ToTType.cutF (A : ToTType) (n : Nat) : Nat → Type :=
  fun m => PProd (m ≤ n) (A.F m)

def cutincl {A : ToTType} (a : A.F n) : (ToTType.cutF A n n) :=
 let p : (n ≤ n) := by omega
 ⟨p, a⟩

def ToTType.cut (A : ToTType) (n : Nat) : ToTType where
  F := cutF A n
  restr := fun m ⟨h, y⟩ =>
   ⟨by exact Nat.le_of_succ_le h, A.restr m y⟩

def ToTType.cutRestr {A : ToTType} {n : Nat} : (cut A n)⤳(cut A (n+1)) where
  val := fun m ⟨h, y⟩ =>
    ⟨by omega, y⟩
  property := by
    intro p
    intro x
    simp
    split
    simp[cut]

def ToTType.Fun (A B : ToTType) : ToTType where
  F := fun n => cut A n ⤳ B
  restr := fun _ h => comp cutRestr h

def ToTType.ev : Prod (Fun A B) A ⤳ B where
  val := fun n => fun fa =>
    let f := (Prod.fst fa).val n
    let a := (Prod.snd fa)
    let xa := cutincl a
    f xa
  property := by
    intro n
    intro fa
    dsimp
--    have xfun := x.fst
--    have xa := cutincl fa.snd
--    have q : x = (xfun,xa) := by sorry
    simp[Prod,Fun,comp,cutRestr,cutincl]
--    let xsnd : (cut A (n + 1)).F (n + 1) := cutincl x.snd
    --let z :
--    let a := (Prod.snd fa)
    let r := fa.fst.property n (cutincl fa.snd) --(by sorry, xa)
    --let p : xa = ⟨_, x.fst⟩ := by omega
--    exact r
    --apply?
    simp[cutincl] at r
    rw[r]
    simp[cut]

def ToTType.lamF (f : Prod A B ⤳ C) (n : Nat) (a : F A n) : cut B n ⤳ C where
  val := fun m b =>
    let p : m ≤ n := b.fst
    let bval : F B m := b.snd
    let a_restr : F A m := restrmap p a
    f.val m (a_restr, bval)
  property := by
      intro m b
      simp
      let h : (m+1 ≤ n) := b.fst
      let y := f.property m (restrmap h a, b.snd)
      rw[y]
      apply congrArg
      simp [Prod]
      constructor
      . apply restrmapEq
      . simp [cut]
        cases b
        simp


def ToTType.lam (f : Prod A B ⤳ C) : A ⤳ Fun B C where
 val := lamF f
 property := by
   intro n x
   let ⟨fval, fprop⟩ := f
   simp [lamF, Fun, comp]
   apply Subtype.valEq
   funext m b
   simp[Prod] at fprop
   simp[· ∘ ·]
   apply congrArg
   ext
   . simp
     apply restrmapEqInner
   . simp
     simp[cutRestr]
     cases b
     simp


def ToTType.deltaFun {A B : Type} (f : A → B) : Γ ⤳ Fun A B :=
  lam (comp snd (delta f))

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
    | succ m p => simp[fixpval,f.property,fixprop,ToTType.Prod]
                  simp[ToTType.Later]
                  --let q := p (Γ.restr (m + 1) γ)
                  exact
                    congrArg (f.val (Nat.succ m))
                      (congrArg (Prod.mk (Γ.restr (Nat.succ m) γ)) (p (Γ.restr (m + 1) γ)))

def fixpoint (A : ToTType) (f : (▷A) ⤳ A) : (Unit ⤳ A)
  := let g : ToTType.Prod Unit (▷A) ⤳ A := ToTType.comp ToTType.snd f;
     fixp g

-- Show fixpoint is fixed point

def ToTType.restrmap_nat (f : Γ ⤳ Δ) (n m : Nat) (p : m ≤ n)(γ : Γ.F n) : f.val m (restrmap p γ) = restrmap p (f.val n γ) :=
 by sorry


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

def ToTType.Str.headFun {A : Type} (str : Γ ⤳ ToTType.Str A) : Γ ⤳ A := comp str head

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
syntax "fun" "(" ident ":" term ")" "=>" ToTExpr : ToTExpr
syntax ToTExpr ToTExpr : ToTExpr
syntax ident : ToTExpr
syntax ToTExpr "::" ToTExpr : ToTExpr
syntax "adv(" ToTExpr ")" : ToTExpr
syntax "delay(" ToTExpr ")" : ToTExpr
syntax "(" ToTExpr ")" : ToTExpr
syntax "head(" ToTExpr ")" : ToTExpr
syntax "box(" ToTExpr ")" : term

structure Ctxt where
  here : Nat := 0
  previous : List Nat := []

def Ctxt.bindvar (c : Ctxt) : Ctxt where
  here := c.here +1
  previous := c.previous

def Ctxt.tick (c : Ctxt) : Ctxt where
  here := 0
  previous := c.here :: c.previous

def Ctxt.untick (c : Ctxt) : Option Ctxt :=
  match c.previous with
  | [] => none
  | x :: xs => some {here := x, previous := xs}

def Ctxt.size (c : Ctxt) : Nat := c.previous.foldl (· + ·) c.here

open Lean Elab Term
def lookup (vars : Ctxt) (index : Nat) : TermElabM (TSyntax `term) :=
  match vars, index with
  | ⟨0,[]⟩ , _ => throwError "No variables in scope"
  | ⟨0, x :: xs⟩ , i => do
    let inner ← lookup ⟨x, xs⟩ i
    `(ToTType.comp ToTType.prev $inner)
  | ⟨k+1, xs⟩ , 0 => `(ToTType.snd)
  | ⟨k+1, xs⟩ , n+1 => do
    let inner ← lookup ⟨k, xs⟩ n
    `(ToTType.comp ToTType.fst $inner)

partial def elabToTExpr (vars : Ctxt) (levels : NameMap Nat) (stx : TSyntax `ToTExpr ) : TermElabM (TSyntax `term) :=
  -- dbg_trace stx
  match stx with
  | `(ToTExpr|[$t]) => `(ToTType.const $t)
  | `(ToTExpr|fix ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr (vars.bindvar) (levels.insert x.getId vars.size) body
    `(fixp (A := $A) $bodyExpr)
  | `(ToTExpr|fun ($x : $A) => $body) => do
    let bodyExpr <- elabToTExpr (vars.bindvar) (levels.insert x.getId vars.size) body
    `(ToTType.lam (B := $A) $bodyExpr)
  | `(ToTExpr|$e1 $e2) => do
    let f <- elabToTExpr vars levels e1
    let a <- elabToTExpr vars levels e2
    `(ToTType.comp (ToTType.pair $f $a) ToTType.ev)
  | `(ToTExpr|$x:ident) => do
    if let some n := levels.find? x.getId then lookup vars (vars.size-n-1)
     else throwErrorAt x "Not a ToT variable"
  | `(ToTExpr|$h :: $t) => do
    let hd <- elabToTExpr vars levels h
    let tl <- elabToTExpr vars levels t
    `(ToTType.Str.cons $hd $tl)
  | `(ToTExpr|adv($d)) => do
    if let some vars' := vars.untick then
      let e <- elabToTExpr vars' levels d -- Todo: Add projection: iterate fst vars.here times
      `(ToTType.adv $e)
    else throwErrorAt stx "No ticks in the context"
  | `(ToTExpr|delay($d)) => do
    let e <- elabToTExpr vars.tick levels d
    `(ToTType.delay $e)
  | `(ToTExpr|head($d)) => do
    let arg <- elabToTExpr vars levels d
    `(ToTType.Str.headFun $arg)
  | `( ToTExpr|($t)) => elabToTExpr vars levels t
  | _ => throwErrorAt stx "Did not understand"

elab_rules : term
  | `( box($t) ) => do
    let f <- elabToTExpr {} {} t
    dbg_trace Syntax.prettyPrint f
    elabTerm f none

#eval (box([4+3]) : Unit ⤳ Nat).val 0 ()

def pretty_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::tl)
def ugly_zeros : Unit ⤳ ToTType.Str Nat := box(fix (tl : _) => [0]::delay(adv(tl)))
def blah : Unit ⤳ Nat := box((fun (x : Nat) => x) [12])
def blahblah : Unit ⤳ Nat := box(((fun (x : Nat) => (fun (y: Nat) => y)) [12]) [14])
def pretty_from : Unit ⤳ (ToTType.Str Nat) :=
--   box(fun (n : _) => fix (f : _) => n ::(f ([ToTType.deltaFun (Nat.succ)] n)))
   box((fix (f : ToTType.Fun Nat (ToTType.Str Nat)) => fun (n : _) => n ::delay(adv(f) n))[5])


#eval blah.val 0 ()
#eval blahblah.val 0 ()
--#eval ToTType.Str.take pretty_zeros 8

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

def ToTType.Str.map {A B : Type} (f : A ⤳ B) : (Str A) ⤳ (Str B) :=
  let appf : (Str A) ⤳ B
    := comp head f;
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

/-- info: [0, 1, 2, 3, 4, 5, 6, 7] -/
#guard_msgs in
#eval ToTType.Str.take (ToTType.Str.natseq) 8

/-- info: [5, 5, 5, 5, 5, 5, 5, 5] -/
#guard_msgs in
#eval ToTType.Str.take pretty_from 8

--#eval ToTType.Str.take zeros 8
/-- info: [0, 0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in
#eval ToTType.Str.take pretty_zeros 8

--#check Nat ⤳ Nat

-- Start of families part

structure ToTType.Fam (Γ : ToTType) where
  F : (n : Nat) → Γ.F (n) → Type
  restr : {n : Nat} → {γ : Γ.F (n + 1)} → F (n+1) γ → F n (Γ.restr n γ)

def ToTType.AsFam (A : ToTType) : Fam Γ where
  F n _ := A.F n
  restr {n} := A.restr n

def ToTType.SubstHelp {A : Fam Γ} {f : Δ ⤳ Γ} {n : Nat} {δ : Δ.F (n+1)} (a : A.F n (Γ.restr n (f.val (n+1) δ)) ) : A.F n (f.val n (Δ.restr n δ)) :=
  f.property n δ ▸ a

def ToTType.Subst (A : Fam Γ) (f : Δ ⤳ Γ) : Fam Δ where
  F n δ := A.F n (f.val n δ)
  restr a := SubstHelp (A.restr a)

def ToTType.Elem (Γ : ToTType) (A : Fam Γ) : Type
    := {f : (n : Nat) → (γ : Γ.F n) → A.F n γ // (∀n γ, A.restr (f (n+1) γ)= f n (Γ.restr n γ))}

def ToTType.AsElem (f : Γ ⤳ A) : Elem Γ (AsFam A) where
   val n γ := f.val n γ
   property := by
     intro n γ
     simp[AsFam]
     exact f.property n γ

def ToTType.Compr (A : Fam Γ) : ToTType where
  F n := (γ : Γ.F n)× (A.F n γ)
  restr n ga := let ⟨γ,a⟩ := ga;
                let γ' := Γ.restr n γ;
                let a' := A.restr a;
                ⟨γ', a'⟩

-- Maybe better to just do logic?

def ToTType.ToTPred (Γ : ToTType) : Type
  := {φ : {n : Nat} → (γ : Γ.F n) → Prop // ∀ n γ, φ γ → φ (Γ.restr n γ)}

def ToTType.AsToTPred (φ : A → Prop) : ToTPred A where
  val := φ
  property := by
    intro n γ
    simp



/-- instance {A : Type} : Coe (A → Prop) (ToTPred A) where
  coe T := { F := fun _ => T, restr := fun _ => id}
  --/

def ToTType.PredSubst (φ : ToTPred Γ) (σ : Δ ⤳ Γ) : ToTPred Δ where
  val {n} δ := φ.val (σ.val n δ)
  property := by
    intro n γ
    simp
    have p := σ.property n γ
    rw[← p]
    exact φ.property n (σ.val (n + 1) γ)


def ToTType.AsToTPred' (φ : A → Prop) (π : Γ ⤳ A): ToTPred Γ :=
  PredSubst (AsToTPred φ) π



def ToTType.PCompr (Γ : ToTType) (φ : ToTPred Γ) : ToTType where
  F n := {γ : Γ.F n // φ.val γ}
  restr n γp := ⟨ Γ.restr n γp.val , φ.property n γp.val γp.property ⟩

def ToTType.PComprPr (φ : ToTPred Γ) : (PCompr Γ φ) ⤳ Γ where
  val := fun n γp => γp.val
  property := by
    simp
    intro n x
    simp[PCompr]

/-- Weakening by a predicate-/
def ToTType.PredWeak (φ ψ : ToTPred Γ) : ToTPred (ToTType.PCompr Γ φ)  := ToTType.PredSubst ψ (PComprPr φ)

def ToTType.TypeWeak (φ : ToTPred Γ) : ToTPred (Prod Γ A) :=
  ToTType.PredSubst φ fst


def ToTType.Proof (Γ : ToTType) (φ : ToTPred Γ) : Prop :=
  ∀ n (γ : Γ.F n), φ.val γ



def ToTType.AsToTProof (p : ∀ x, φ x) : Proof _ (AsToTPred φ) :=
  by
    simp[Proof]
    intro n γ
    simp[AsToTPred]
    exact p γ


-- The next one reintroduces sequents under different name
def ToTType.ProofImpl (φ ψ : ToTPred Γ) : Prop :=
  Proof _ (PredWeak φ ψ)

-- Forget about sequents, use Proof
/--
def ToTType.Sequent (φ ψ : ToTPred Γ) : Prop
  := ∀ n (γ : Γ.F n), (φ.val γ) → (ψ.val γ)

def ToTType.SeqTrivial : Sequent φ φ :=
  by
    sorry

def ToTType.SeqComp (ρ φ ψ : ToTPred Γ) (p : Sequent ρ φ) (q : Sequent φ ψ) : Sequent ρ ψ :=
  by
   simp[Sequent]
   intro n γ
   intro a
   exact (q n γ (p n γ a))

-/

def ToTType.Conj (φ ψ : ToTPred Γ) : ToTPred Γ where
  val γ := φ.val γ ∧ ψ.val γ
  property := by
    intro n γ
    simp
    intro  p q
    constructor
    . exact φ.property n γ p
    . exact ψ.property n γ q

def ToTType.ConjIntro (p : Proof _ φ) (q : Proof _ ψ) : Proof _ (Conj φ ψ) :=
  by sorry

def ToTType.ConjElimL (p : Proof _ (Conj φ ψ)) : Proof _ φ :=
  by sorry

def ToTType.ConjElimR (p : Proof _  (Conj φ ψ)) : Proof _  ψ :=
  by sorry

def ToTType.Impl (φ ψ : ToTPred Γ) : ToTPred Γ where
 val {n} γ := ∀ m, (p : m ≤ n) → φ.val (restrmap p γ) → ψ.val (restrmap p γ)
 property := by
   intro n γ q m p r
   have s := restrmapEqInner (m:=m) (n:= n) (by omega) p γ
   rw[← s] at r
   have t := q m (by omega) r
   rw[s] at t
   exact t

def ToTType.ImplIntro (p : Proof  (Γ := PCompr Γ φ) (PredWeak φ ψ)) : Proof _  (Impl φ ψ) :=
  by
   simp_all[Proof]
   intro n γ
   -- apply p n
   simp[Impl]
   intro m q r
   simp_all[PCompr,PredSubst,PComprPr]
   exact p m (⟨restrmap q γ, r ⟩)

/--
def ToTType.ConjIntro (ρ φ ψ : ToTPred Γ) (p : Sequent ρ φ) (q : Sequent ρ ψ) : Sequent ρ (Conj φ ψ) :=
  by
    simp[Sequent]
    intro n γ r
    simp[Conj]
    constructor
    . exact p n γ r
    . exact q n γ r

def ToTType.ConjElimL (ρ φ ψ : ToTPred Γ) (p : Sequent ρ (Conj φ ψ)) : Sequent ρ φ :=
  by
    simp[Sequent]
    intro n γ q
    have r := p n γ q
    let ⟨r1 , _ ⟩ :=  r
    exact r1

def ToTType.ConjElimR (ρ φ ψ : ToTPred Γ) (p : Sequent ρ (Conj φ ψ)) : Sequent ρ ψ :=
  by
    simp[Sequent]
    intro n γ q
    have r := p n γ q
    let ⟨ _ , r2 ⟩ :=  r
    exact r2
-/

def ToTType.Forall (φ : ToTPred (Prod Γ Δ)) : ToTPred Γ where
  val {n} γ := ∀ m, (p : m≤ n) → ∀ δ , φ.val ⟨ restrmap p γ , δ ⟩
  property := by
    intro n γ
    simp
    intro q
    intro m p δ
    have r := q m (by omega) δ
    have s := restrmapEqInner (m:=m) (n:= n) (by omega) p γ
    rw[s] at r
    exact r


def ToTType.prodOverCompr : PCompr (Γ := (Prod Γ Δ)) (PredSubst φ fst) ⤳ Prod (PCompr (Γ := Γ) φ) Δ where
  val n γ' :=
    let ⟨(γ, δ), p⟩ := γ'
    (⟨γ, p⟩, δ)
  property := by
    intro n x
    let ⟨(γ, δ), p⟩ := x
    simp[PCompr, PredSubst,Prod]

def ToTType.comprOverProd : Prod (PCompr (Γ := Γ) φ) Δ ⤳ PCompr (Γ := (Prod Γ Δ)) (PredSubst φ fst) where
  val n γ' :=
    let ⟨⟨γ, p⟩, δ⟩ := γ'
    ⟨(γ, δ), p⟩
  property := by
    intro n x
    let ⟨⟨γ, p⟩, δ⟩ := x
    simp[PCompr, PredSubst,Prod]

def isConst (f : α → β) := ∃ (y : β), ∀ (x : α), f x = y

def isConst' (f : α → β) := ∀ x y, f x = f y



@[simp]
theorem ToTType.cast_eq : HEq (cast h a) a := by
  cases h
  simp [cast]


theorem eq_rec_trans (x : γ) (p1 : α = β) (p2 : β = γ) : p1 ▸ p2 ▸ x = (p1.trans p2) ▸ x := by
  cases p1
  simp

theorem ToTType.restrmaphelp_const {A : ToTType} (c : isConst' A.F) (a : A.F (n + k)) :
    (∀ n x, A.restr n x = (c _ _).mp x) → restrmaphelp n k a = (c _ _).mp a := by
  intro constRestr
  induction k generalizing n with
  | zero =>
    have := restrmaphelpzero n 0 rfl rfl a
    simp only [Nat.add_zero, cast_refl_id] at this; trivial
  | succ k' ih =>
    have := restrmaphelpsucc n (k' + 1) rfl (by omega) a
    rw [this]
    have h : n + (k' + 1) = n + 1 + k' := by omega
    have := constRestr n (restrmaphelp (n + 1) k' (cast h a))
    simp_all only; clear this
    simp [Eq.mp]
    rw [eq_rec_trans] <;> try (apply c)
    have : A.F (n + (k' + 1)) = A.F (n + 1 + k') := by apply c
    congr 1
    . apply c
    . rw [h]
    . apply cast_eq
    . rw [h]



theorem ToTType.restrmap_const_id (A : ToTType) (c : isConst' A.F) :
    (∀ n x, A.restr n x = (c _ _).mp x) → (x : A.F m) →
    restrmap (m := n) (A := A) p x = (c _ _) ▸ x := by
  intro constRestr
  intros
  simp [restrmap]
  rw [restrmaphelp_const] <;> try trivial
  congr 1
  . apply c
  . exact heq_of_eqRec_eq (congrFun (congrArg Eq (c (n + (LThelp m n p).val) m)) (A.F n)) rfl
  . exact cast_eq


def ToTType.PredWeakForall {φ : ToTPred Γ} {ψ : ToTPred (Γ.Prod A)} :
    Proof _  (PredWeak φ (Forall ψ)) ↔ Proof _  (Forall (PredSubst (PredWeak (PredSubst φ fst) ψ) comprOverProd))
  := by
  constructor
  . intro p
    simp[Proof, Forall, PredSubst, PredWeak,PComprPr, comprOverProd]
    intro n γ m m_le_n δ
    simp[Proof, Forall, PredSubst, PredWeak,PComprPr, comprOverProd] at p
    let r := p n γ m m_le_n δ
    simp[Prod,PCompr]
    let s := restrmap_nat (PComprPr φ) n m m_le_n γ
    simp[PComprPr] at s
    rw[s]
    exact r
  . intro h
    intro n γ
    simp [PredWeak, PredSubst, Forall, PComprPr]
    intro m m_le_n δ
    have r := restrmap_nat (PComprPr φ) n m m_le_n γ
    simp [PComprPr] at r
    simp [PCompr, Proof, PredSubst, Forall, PredWeak] at γ h
    have := h n γ m m_le_n δ
    simp [PComprPr, comprOverProd] at this
    rw[r] at this
    exact this










def ToTType.ForallCl (φ : ToTPred Γ) : ToTPred Unit :=
  Forall (PredSubst φ snd)

def ToTType.ForallIntro {φ : ToTPred (Prod Γ A)} (p : Proof _  φ) : Proof (Γ := Γ) (Forall φ) :=
  by sorry

def ToTType.ForallIntroCl (p : Proof _  φ) : Proof _  (ForallCl φ) :=
  by sorry

def ToTType.ForallElim {φ : ToTPred (Prod Γ Δ)} (p : Proof _  (Forall φ)) : Proof _  φ :=
  by sorry

def ToTType.ForallElimCl (p : Proof _  (ForallCl φ)) : Proof _  φ :=
  by sorry

/--
def ToTType.ForallIntro (p : Sequent (PredSubst φ fst) ψ) : Sequent φ (Forall ψ) :=
  by
    sorry

def ToTType.ForallElim (p : Sequent φ (Forall ψ)) : Sequent (PredSubst φ fst) ψ :=
  by
    sorry

def ToTType.ForallClIntro (p : Sequent (PredSubst φ fst) ψ) : Sequent φ (ForallCl ψ) :=
  by
    sorry

def ToTType.ForallClElim (p : Sequent φ (ForallCl ψ)) : Sequent (PredSubst φ fst) ψ :=
  by
    sorry
-/

def ToTType.True (Γ : ToTType) : ToTPred Γ where
  val γ := true
  property := by
    intro n _
    simp

def ToTType.Top {Γ : ToTType} : Proof _  (True Γ) :=
  by
    simp[Proof]
    intro n γ
    simp[True]

structure ToTType.proofsOf (φ : Prop) : Type where
  proof : φ
--{ x : Unit // φ}

def ToTType.proofsOfEl (φ : Prop) (p : φ) : (proofsOf φ) := ⟨ p ⟩

def ToTType.proofsOfImp (p : φ → ψ) (x : proofsOf φ) : (proofsOf ψ) :=
  let ⟨ q ⟩ := x
  ⟨ p q ⟩
--  proofsOfEl ψ (p (x.property))
--  val := x.val
--  property := p x.property

def ToTType.UnitSet (x y : Unit) : x=y :=
  by
   ext

@[simp]
def ToTType.proofsOfSet (x y : proofsOf φ) : x = y :=
  by
   cases x
   cases y
   rfl

def ToTType.Yoneda (n : Nat) : ToTType where
  F {m} := proofsOf (m ≤ n)
  restr m := proofsOfImp (by omega)

def ToTType.YonMap (p : m ≤ n) : (Yoneda m) ⤳ (Yoneda n) where
  val o q := proofsOfEl (o ≤ n) (by let r : (o ≤ m) := q.proof ; omega)
  property := by
    intro n x
    apply proofsOfSet


def ToTType.ToTProp : ToTType where
  F n := ToTPred (Yoneda n)
  restr n φ :=
    let f : (Yoneda n) ⤳ (Yoneda (n+1)) := YonMap (by omega)
    PredSubst φ f

-- PredPi Γ is the Π type Π Γ ToTProp
-- def ToTType.PredPi (Γ : ToTType) : ToTType where
--   F n := ToTPred (Prod Γ (Yoneda n))
--   restr n φ :=
--     let f : (Prod Γ (Yoneda n)) ⤳ (Prod Γ (Yoneda (n+1))) := ProdHom ToTType.id (YonMap (by omega))
--     PredSubst φ f

def ToTType.Code (φ : ToTPred Γ) : Γ ⤳ ToTProp where
  val n γ :=
    let ψ := fun {m} y => φ.val (restrmap y.proof γ)
    let prop : ∀ (m : Nat) (ρ : (Yoneda n).F (m+1)) , ψ ρ → ψ ((Yoneda n).restr m ρ) :=
      by
       intro m ρ p
       simp[ψ]
       simp[ψ] at p
       let q := φ.property m _ p
       let mn := ρ.proof
       let r:= @ToTType.restrmapEq m n Γ mn (by omega) γ
       rw [← r]
       apply q
    ⟨ ψ , prop ⟩
  property := by
    sorry

def ToTType.PropEl : ToTPred Γ := True Γ

def ToTType.PropElem (f : Γ ⤳ ToTProp) : ToTPred Γ  :=
  PredSubst PropEl f

/- def ToTType.PLaterVal (φ : ToTPred (◁ Γ)) : {n : Nat} → (γ : Γ.F n) → Prop
  | 0, _ => true
  | _+1, γ => φ.val γ

def ToTType.PLater (φ : ToTPred (◁ Γ)) : ToTPred Γ where
  val := PLaterVal φ
  property := by
    intro n
    cases n
    . simp[PLaterVal]
    . simp[PLaterVal]
      apply φ.property
 -/

def ToTType.PLaterVal (φ : ToTPred Γ) : {n : Nat} → (γ : (▷ Γ).F n) → Prop
  | 0, _ => true
  | _+1, γ => φ.val γ

def ToTType.PLater (φ : ToTPred Γ) : ToTPred (▷ Γ) where
  val := PLaterVal φ
  property := by
    intro n
    cases n
    . simp[PLaterVal]
    . simp[PLaterVal]
      apply φ.property

def ToTType.PLaterFib (φ : ToTPred Γ) : ToTPred Γ :=
  PredSubst (PLater φ) next

def ToTType.PLatBind (φ : ToTPred (◁ Γ)) : ToTPred Γ :=
  PredSubst (PLater φ) (delay  (ToTType.id))

def ToTType.PEarlier (φ : ToTPred Γ) : ToTPred (◁ Γ) where
  val := φ.val
  property := by
    intro n γ
    apply (φ.property (n+1) γ)


-- def ToTType.Pfix (p : Sequent (Conj φ (PredSubst (PLater ψ) ToTType.next)) ψ) : Sequent φ ψ  :=
def ToTType.Pfix (φ : ToTPred Γ) (p : Proof (PCompr (Γ := Γ) (PLaterFib φ)) (PredWeak (PLaterFib φ) φ)) : Proof Γ φ  :=
  by
    sorry

/-- def ToTType.PfixCl (p : Sequent (PredSubst (PLater ψ) ToTType.next) ψ) : Sequent True ψ :=
  -- Pfix (SeqComp (ConjElimR (Conj True (PredSubst (PLater ψ) ToTType.next)) True (PredSubst (PLater ψ) ToTType.next) SeqTrivial) p)
  by
    sorry
--/

def ToTType.PLaterProp : ToTPred (▷ ToTProp) := PLater (True ToTProp)

--def ToTType.PBox (φ : ToTPred Γ) (γ : Box Γ) : Prop :=
-- Sequent True φ

def ToTType.PredLiftStr {A : Type} (ψ : A → Prop) : ToTPred (ToTType.Str A) :=
  let φ := AsToTPred ψ
  let hd : (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) ⤳ A := comp snd Str.head
  let tl : (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) ⤳ (▷ (Str A)) := comp snd Str.tail
  let tlcond : ToTPred (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) := PredSubst PLaterProp (comp (pair fst tl) appfun)
  let help : ToTPred (Prod (▷ (Fun (Str A) ToTProp)) (Str A)) := Conj (PredSubst φ hd) tlcond
  let helper : (▷ (Fun (Str A) ToTProp)) ⤳ (Fun (Str A) ToTProp) := lam (Code help)
  let f : Unit ⤳ (Fun (Str A) ToTProp) := (fixpoint (Fun (Str A) ToTProp) helper)
  let g : (Str A)  ⤳ ToTProp := comp (pair (comp unitFinal f) id) ev
  PropElem g

-- def ToTType.PredLiftStrFold : Sequent (Conj (PredSubst φ hd) (PredSubst (PLater (PredLiftStr φ)) Str.tail)) (PredLiftStr φ) :=
  def ToTType.PredLiftStrFold (p : Proof _  (PredSubst (AsToTPred φ) hd)) (q : Proof _  (PredSubst (PLater (PredLiftStr φ)) Str.tail)) : Proof _  (PredLiftStr φ) :=
    by sorry

-- def ToTType.PredLiftStrHelp {φ : A → Prop} (p : forall a, φ a)
--    : ProofImpl (PLaterFib (ForallCl (PredLiftStr φ))) (ForallCl (PredLiftStr φ))
--    :=
--   let hdproof : ProofImpl (PredSubst (PLaterFib (ForallCl (PredLiftStr  φ))) fst) (PredSubst (AsToTPred φ) Str.head) :=
--     by
--       sorry
--   let tlproof : ProofImpl (PredSubst (PLaterFib (ForallCl (PredLiftStr φ))) fst) (PredSubst (PLater (PredLiftStr φ)) Str.tail) :=
--     by
--       sorry
--   ForallIntro (PredLiftStrFold hdproof tlproof)



-- def ToTType.PredLiftStrProof (p : Proof _  φ) : Proof _  (ForallCl (PredLiftStr φ)) :=
--  ForallIntroCl (Pfix _)

-- Add tail condition to the below
def ToTType.PredLiftStrPretty  {A : Type} : Box (((A : ToTType).Fun ToTProp).Fun ((ToTType.Str A).Fun ToTProp)) :=
  box(fun (φ : _) => fix (ψ : ((Str A).Fun ToTProp)) => fun (xs : _)  => φ (head(xs)))

-- axiom LiftPredStr {Γ} {A} : (φ : A → Prop) → ToTType.ToTPred (ToTType.Prod Γ (ToTType.Str A))

axiom LiftPredStr {A} {Γ} : (φ : A → Prop) → (π : Γ ⤳ ToTType.Str A) → ToTType.ToTPred Γ

axiom ToTType.PredSubstIntoLiftPredStr {A} {Γ} {Δ} : (φ : A → Prop) → (π : Γ ⤳ ToTType.Str A) → (σ : Δ ⤳ Γ) → (PredSubst (LiftPredStr φ π) σ) = LiftPredStr φ (comp σ π)
-- Use of equality is justified by Prop-ext and fun-ext from the def of ToTPred

-- axiom ToTType.LiftPredStrCompOverProd {Γ} {A} {φ : A → Prop} {ψ : ToTPred Γ} : Proof (Prod (PCompr Γ ψ) (Str A)) (PredSubst (LiftPredStr φ) (pair unitFinal snd)) ↔
--   Proof (Prod (PCompr Γ ψ) (Str A)) (PredSubst (PredWeak (TypeWeak ψ) (PredSubst (LiftPredStr φ) (pair unitFinal snd))) comprOverProd)

-- axiom ToTType.LiftPredStrWeak {Γ} {A} {φ : A → Prop} {ψ : ToTPred Γ} : Proof (Prod (PCompr (Γ := Γ) ψ) (ToTType.Str A)) (LiftPredStr φ)
--    → Proof (PCompr (Γ := Prod Γ (Str A)) (TypeWeak ψ)) (PredWeak (TypeWeak ψ) (LiftPredStr (Γ := Γ) φ))

-- axiom ToTType.LiftPredStrCompOverProd {Γ} {A} {φ : A → Prop} {ψ : ToTPred Γ} : Proof (Prod (PCompr Γ ψ) (Str A)) (LiftPredStr φ) ↔
--   Proof (Prod (PCompr Γ ψ) (Str A)) (PredSubst (PredWeak (TypeWeak ψ) (LiftPredStr φ)) comprOverProd)

-- axiom ToTType.LiftPredSubst {Γ Δ : ToTType} {σ : Δ ⤳ Γ} {A} {φ : A → Prop} :
--  Proof (Prod Δ (Str A)) (PredSubst (LiftPredStr (Γ := Γ) φ) (ProdHom σ ToTType.id)) ↔ Proof (Prod Δ (Str A)) (LiftPredStr (Γ := Δ) φ)

declare_syntax_cat ctxt
declare_syntax_cat ctxt_elem
declare_syntax_cat stmt
syntax "✓" : ctxt_elem
syntax (name:=binder) ident " ∈ " term : ctxt_elem
syntax ident " : " stmt : ctxt_elem
syntax ctxt_elem : ctxt
syntax "·" : ctxt
syntax ctxt ", " ctxt_elem : ctxt

syntax stmt " → " stmt : stmt
syntax ident : stmt
syntax "∀ " ident ", " stmt : stmt
syntax "∀ " ident " : " term ", " stmt : stmt
syntax "[" term "] " ident* : stmt -- apply ToT-pred in Lean syntax to arguments
syntax "(" stmt ")" : stmt
syntax "↑" term : stmt -- lift predicate to stream
syntax "![" ctxt " | " stmt "]" : term
syntax "!{" ctxt "}" : term
syntax "![" stmt "]" : term
syntax "¡" ctxt " | " ident* "!" : term
/-- Variable projection -/
syntax "¡¡" ctxt " | " ident "!!" : term
syntax "¡" ctxt "€" ident "!" : term

declare_syntax_cat tot_proof_state
syntax (ctxt_elem ppLine)* "⊨ " stmt : tot_proof_state
namespace Internals
scoped syntax (name:=embedProof) tot_proof_state : term
end Internals

open Lean in
macro_rules
  | `(¡ $_ | !) => `((ToTType.unitFinal ))
  | `(¡ $Γ | $xs:ident* $x:ident !) => `(ToTType.pair ¡ $Γ | $xs* ! ¡ $Γ € $x !)
  | `(¡ · € $x !) => Macro.throwErrorAt x s!"Unknown: {x}"
  | `(¡ $y:ident ∈ $_:term € $x:ident !) =>
    if x.getId == y.getId then
      `(ToTType.snd)
    else Macro.throwErrorAt x s!"Unknown: {x}"
  | `(¡ $Γ, $y:ident ∈ $_:term € $x:ident !) =>
    if x.getId == y.getId then
      `(ToTType.snd)
    else ``(ToTType.comp ToTType.fst ¡ $Γ € $x !)

open Lean in
macro_rules
  | `(¡¡ · | $x !!) => Macro.throwErrorAt x s!"Unknown: {x}"
  | `(¡¡ $y:ident ∈ $_:term | $x:ident !!) =>
    if x.getId == y.getId then
      `(ToTType.snd)
    else Macro.throwErrorAt x s!"Unknown: {x}"
  | `(¡¡ $Γ, $y:ident ∈ $_:term | $x:ident !!) =>
    if x.getId == y.getId then
      `(ToTType.snd)
    else ``(ToTType.comp ToTType.fst ¡¡ $Γ | $x !!)



macro_rules
  | `(![$Γ | ($s)]) => `(![$Γ | $s])
  | `(![$s]) => `(![· | $s])
  | `(![ $Γ | $s1 → $s2]) => `(ToTType.Impl ![$Γ | $s1] ![$Γ | $s2])
  | `(![ $Γ | ∀ $x:ident, $s:stmt]) =>
    `(let t := _; ToTType.Forall (Δ := t) ![$Γ, $x:ident ∈ t | $s])
  | `(![ $Γ | ∀ $x:ident : $t, $s]) =>
    `(let t := $t; ToTType.Forall (Δ := t) ![$Γ, $x:ident ∈ t | $s])
  | `(![ $_ | True]) => `(ToTType.True _)
  | `(![ $Γ | [ $pred ] $arg]) =>
    `(term| $pred (¡¡ $Γ | $arg !!)) -- Update later to allow multiple arguments
  | `(!{·}) => ``((Unit : ToTType))
  | `(!{✓}) => ``((◁ Unit : ToTType))
  | `(!{$Γ:ctxt, ✓}) => ``((◁ !{$Γ} : ToTType))
  | `(!{$x:ident ∈ $t}) => ``((ToTType.Prod Unit $t : ToTType))
  | `(!{$Γ, $x:ident ∈ $t}) =>
    ``((ToTType.Prod !{$Γ} $t : ToTType))
  | `(!{$x:ident : $t}) => ``((@ToTType.PCompr Unit ![· | $t] : ToTType))
  | `(!{$Γ:ctxt, $x:ident : $t}) =>
    ``((@ToTType.PCompr !{$Γ} ![$Γ | $t] : ToTType))
/-- info: { F := fun x => Unit, restr := fun x => id } : ToTType -/
#guard_msgs in
#check !{·}

/--
info: { F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id } : ToTType
-/
#guard_msgs in
#check !{x ∈ Nat}

/--
info: (◁({ F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id }).Prod
        { F := fun x => String, restr := fun x => id }).Prod
  { F := fun x => Nat, restr := fun x => id } : ToTType
-/
#guard_msgs in
#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat}
set_option guard_msgs.diff true
/--
info: ((◁({ F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id }).Prod
            { F := fun x => String, restr := fun x => id }).Prod
      { F := fun x => Nat, restr := fun x => id }).PCompr
  ((◁({ F := fun x => Unit, restr := fun x => id }.Prod { F := fun x => Nat, restr := fun x => id }).Prod
            { F := fun x => String, restr := fun x => id }).Prod
      { F := fun x => Nat, restr := fun x => id }).True : ToTType
-/
#guard_msgs in
#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat, t : True}

#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat, t : ∀ x, True}

#check !{x ∈ Nat, y ∈ String, ✓, z ∈ Nat, t : ∀ x : Int, True}

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabArgs : DelabM (TSyntaxArray `ident) := do
  let e ← getExpr
  match_expr e with
  | ToTType.unitFinal _ => pure #[]
  | ToTType.pair _ _ _ _ _ =>
    let pre ← withAppFn <| withAppArg delabArgs
    let me ← withAppArg <| annAsTerm <| ← `(ident|x)
    return pre.push me
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabMorph : DelabM (TSyntaxArray `ident) := do
  let e ← getExpr
  match_expr e with
  | ToTType.unitFinal _ => pure #[]
  | ToTType.pair _ _ _ _ _ =>
    let pre ← withAppFn <| withAppArg delabArgs
    let me ← withAppArg <| annAsTerm <| ← `(ident|x)
    return pre.push me
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabStmtInner : DelabM (TSyntax `stmt) := do
  let e ← getExpr
  let stx ←
    match e with
    | .letE _ _ _ body _ => withLetBody delabStmtInner
    | _ =>
    match_expr e with
    | ToTType.Impl _ _ _ =>
      let s1 ← withAppFn <| withAppArg delabStmtInner
      let s2 ← withAppArg delabStmtInner
      `(stmt| $s1 → $s2)
    | ToTType.Forall _ _ _ =>
      let x := mkIdent (← mkFreshBinderName)
      let body ← withAppArg delabStmtInner
      `(stmt| ∀ $x, $body)
    | ToTType.PredSubst _ _ _ _ =>
      let pred ← withAppFn <| withAppArg delab
      let args ← withAppArg delabArgs

      `(stmt| [$pred] $args*)
    | ToTType.PredWeak _ _ _ =>
      withAppArg delabStmtInner
    | _ =>
      `(stmt| [$(← delab)])
  annAsTerm stx

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
partial def delabProofCtxt : DelabM (TSyntaxArray `ctxt_elem) := do
  match_expr ← getExpr with
  | ToTType.PCompr _ _ =>
    let Γ ← withAppFn <| withAppArg delabProofCtxt
    let φ ← withAppArg do delabStmtInner
    return Γ.push (← withAppArg <| annAsTerm (← `(ctxt_elem|x : $φ)))
  | ToTType.mk _ _ =>
    withAppFn <| withAppArg do
      match (← getExpr) with
      | .lam _ _ _ _ =>
        withBindingBody `x do
          match_expr (← getExpr) with
          | Unit =>
            pure #[]
          | _ =>
          failure
      | _ => failure
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
open Internals in
@[delab app.ToTType.Proof]
partial def delabProof : Delab := do
  match_expr ← getExpr with
  | ToTType.Proof _ _ =>
    let stmt ← withAppArg delabStmtInner
    let ctxt ← withAppFn <| withAppArg delabProofCtxt
    let prf ← `(tot_proof_state| $[$ctxt]* ⊨ $stmt)
    pure ⟨prf.raw⟩
  | _ => failure

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer in
@[delab app.ToTType.Impl, delab app.ToTType.Forall, delab app.ToTType.PredSubst, delab app.ToTType.PredWeak]
partial def delabStmt : Delab := do
  -- This delaborator only understands a certain arity - give up if it's incorrect
  guard <| match_expr ← getExpr with
    | ToTType.Impl _ _ _ => true
    | ToTType.Forall _ _ _ => true
    | ToTType.PredSubst _ _ _ _=> true
    | ToTType.PredWeak _ _ _ => true
    | _ => false
  match ← delabStmtInner with
  | `(stmt|[$e]) => pure e
  | e => `(term|![$(⟨e⟩)])


namespace Internals
scoped syntax "builtinIntro" : tactic
macro_rules | `(tactic|builtinIntro) => `(tactic|intro)
end Internals

syntax (name := ourIntro) "intro" : tactic

open ToTType in
open Internals in
macro_rules (kind := ourIntro)
  | `(tactic|intro) =>
    `(tactic|first | apply ImplIntro | apply ForallIntro | builtinIntro)



-- theorem ToTType.liftOk (φ : A → Prop) : Proof _ (Impl (ForallCl (AsToTPred φ)) (ForallCl (LiftPredStr φ))) := sorry

theorem ToTType.liftOk' (φ : A → Prop) : Proof (Γ := Unit) ![ (∀ x : A, [AsToTPred' φ] x) → (∀ xs : Str A, [LiftPredStr φ] xs) ] := by
  intro
  rw [PredWeakForall]
  set_option pp.explicit true in
  conv =>
    congr
    congr
    -- Stuck here. Todo 5/11: move PredWeak under LiftPredStr
    rw [PredSubstIntoLiftPredStr φ snd]
  apply Pfix
  rw [PredWeakForall]
  apply ForallIntro
  rw[PredSubstIntoLiftPredStr φ snd]
  simp
  have := @LiftPredStrCompOverProd Unit A φ
  rw [← LiftPredStrCompOverProd]
  -- Stuck here
  apply LiftPredStrWeak
  sorry

-- @Proof ?Γ (![∀ x✝, [?φ] ]) : Prop

--    @Forall ?Γ ?A ?φ : ?Γ.ToTPred

-- @Proof
--   (PCompr
--     (let t := A;
--     ![∀ x✝, [AsToTPred' φ] x✝]))
--   (![∀ x✝, [LiftPredStr φ] x✝]) : Prop

--    @PredWeak { F := fun x => Unit, restr := fun x => _root_.id }
--     (let t := A;
--     ![∀ x✝, [AsToTPred' φ] x✝])
--     (let t := Str A;
--     ![∀ x✝, [LiftPredStr φ] x✝]) : (PCompr
--       (let t := A;
--       ![∀ x✝, [AsToTPred' φ] x✝])).ToTPred

theorem ToTType.liftOk'AfterIntro (φ : A → Prop) :
    Proof (Γ := ToTType.PCompr (Γ := Unit) ![(∀ x : A, [AsToTPred' φ] x)]) ![ (∀ xs : Str A, [LiftPredStr φ] xs) ] := by
  skip

-- TODO next time: we just finished intro tactic for implication, next time do it for universal quantification. Current progress: weakening is getting in the way. We think we need PredWeakForall above, but didn't finish it.

/-
  Sketch proof using tactics:
   Assumption: φ : A → Prop
   Construct LiftPredStr φ : Pred (Str A) such that LiftPredStr φ (xs) equivalent to
   φ(hd(xs)) ∧ ▷ LiftPredStr φ (adv(tl(xs)))
   Want to prove
   (∀ x, φ (x)) → ∀ xs, LiftPredStr φ xs
   Proof should proceed as follows:
     intro p
     guarded_recursion
       At this point the context should be
         p : ∀ x, φ (x)
         IH : ▷ (∀ xs, LiftPredStr φ xs)
     intro xs
     [Something to unfold LiftPredStr φ xs]
    constructor/conjIntro  (not sure what the tactic name is, need to prove conjunction)
     . apply p
     . tickintro
         At this point context is
            p : ∀ x, φ (x)
            IH : ▷ (∀ xs, LiftPredStr φ xs)
            xs : Str A
            tick
          Must prove
          LiftPredStr φ (adv(tl(xs)))
        exact (adv IH (adv (tl(xs))))

  -/
