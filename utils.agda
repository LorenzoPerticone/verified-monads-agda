module utils where
  infixr 20 _∘_
  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

  id : {A : Set} → A → A
  id x = x

  infixl 20 _$_
  _$_ : {A B : Set} → (A → B) → A → B
  f $ x = f x

  ev : {A B : Set} → A → (A → B) → B
  ev x f = f x
