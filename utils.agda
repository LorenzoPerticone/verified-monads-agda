module utils where
  infixr 20 _∘_
  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

  id : {A : Set} → A → A
  id x = x
