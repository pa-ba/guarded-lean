import Std

universe u


inductive Ctx : Type u → Type (u + 1) where
  | empty : Ctx PUnit
  | snoc : (Γ : Ctx γ) → (α : γ → Type) → Ctx (Σ (v : γ), α v)

example : Ctx PUnit := .empty

example : Ctx (Σ _ : PUnit, Nat) := .snoc .empty fun () => Nat


example : Ctx (Σ v : (Σ _ : PUnit, Nat), Fin (v.snd)) := .snoc (.snoc .empty fun () => Nat) (fun ⟨_,n⟩ => Fin n)

-- axiom Later' : {γ : Type u} → (dsubst : Ctx γ → Type (u+1)) → (ξ : dsubst γ)  → (β : γ → Type u) → Type (u + 1)


-- def DSubst : {γ : Type} →  Ctx γ → Type 1
--   | _, .empty => PUnit
--   | .(Sigma α), .snoc Γ α => Σ (ξ : DSubst Γ) , α _


def DSubst : {γ : Type} →  Ctx γ → Type 1 := by
  intro γ Γ
  cases Γ with
  | empty => exact PUnit
  | snoc Γ α => let foo := DSubst Γ 
                _


-- mutual
--   inductive DSubst : Type u → Type (u + 1) where
--   | empty : DSubst PUnit
--   | snoc : {α : Type u} → (ξ : DSubst α) → (β : α → Type u) → Later' DSubst ξ β → DSubst (Σ x : α, β x)

-- end

-- axiom next : {α : Type u} → {β : α → Type u} → (ξ : DSubst α) → ((x:α) → β x) → Later ξ β

-- noncomputable def dmap (f : α → β) (x : Later α) : Later β
--   := next (.cons x fun x' => .empty (f x'))

-- noncomputable def next' (x : α) : Later α
--   := next (.empty x)

-- noncomputable def app (f : Later (α → β)) (x : Later α) : Later β
--   := next (.cons f fun f' => .cons x fun x' => .empty (f' x'))

-- infixl:65   " <*> " => app

-- axiom Fix : (f : Type → Type) → Type

-- axiom Fix_beta : (f : Type → Type) → Fix f = f (Later (Fix f))

-- axiom fix : {α : Type} → (f : Later α → α) → α

-- def Str (α : Type) : Type := Fix (fun T => α × T)

-- def Str.unfold (s : Str α) : α × Later (Str α) := Fix_beta (fun T => α × T) ▸ s


-- def Str.head (s : Str α) : α := s.unfold.fst
-- def Str.tail (s : Str α) : Later (Str α) := s.unfold.snd

-- def Str.cons {α : Type} (x : α ) (xs : Later (Str α )) : Str α :=
--   let xs' : Fix (fun T => α × T) :=  (Fix_beta (fun T => α × T)) ▸ (x , xs)
--   xs'

-- infixr:65   " :: " => Str.cons

-- axiom fix_beta : {α : Type} → {f : Later α → α} → fix f = f (next' (fix f ))

-- noncomputable def zeros : Str Nat := fix (fun x => 0 :: x)

-- theorem zeros_unfold : zeros = .cons 0 (next' zeros) := by
--   simp [zeros]
--   conv => lhs ; rw [fix_beta]

-- noncomputable def map {α β : Type} (f : α → β) : Str α → Str β :=
--   fix fun r => fun xs => f xs.head :: (r <*> xs.tail)
