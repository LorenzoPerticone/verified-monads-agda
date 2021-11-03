module maybe where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils
  open import definitions

  data Maybe : Set → Set where
    nothing : {A : Set} → Maybe A
    just : {A : Set} → A → Maybe A

  mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
  mapMaybe f nothing = nothing
  mapMaybe f (just x) = just (f x)

  mapReplaceMaybe : {A B : Set} →
                    (f : A → B) → (g : A → B) →
                    ((x : A) → f x ≡ g x) →
                    (y : Maybe A) →
                    mapMaybe f y ≡ mapMaybe g y
  mapReplaceMaybe f g p nothing = refl
  mapReplaceMaybe f g p (just x) = cong just (p x)

  ax1Maybe : {A : Set} → (x : Maybe A) →
             mapMaybe id x ≡ x
  ax1Maybe nothing = refl
  ax1Maybe (just x) = cong just refl

  ax2Maybe : {A B C : Set} → (f : B → C) → (g : A → B) →
             (x : Maybe A) →
             mapMaybe (f ∘ g) x ≡ mapMaybe f (mapMaybe g x)
  ax2Maybe f g nothing = refl
  ax2Maybe f g (just x) = cong just refl 

  𝑀aybe : Functor Maybe
  𝑀aybe = functor mapMaybe mapReplaceMaybe ax1Maybe ax2Maybe

  unitMaybeMorp : {A : Set} → Id A → Maybe A
  unitMaybeMorp x = just x

  unitMaybeAxNat : {A B : Set} → (f : A → B) → (x : Id A) →
                   mapMaybe f (unitMaybeMorp x) ≡ unitMaybeMorp (mapF 𝟙 f x)
  unitMaybeAxNat f x = refl

  unitMaybe : 𝟙 ~> 𝑀aybe
  unitMaybe = NT unitMaybeMorp unitMaybeAxNat

  multMaybeMorp : {A : Set} → (Maybe <> Maybe) A → Maybe A
  multMaybeMorp nothing = nothing
  multMaybeMorp (just x) = x

  multMaybeAxNat : {A B : Set} → (f : A → B) → (x : (Maybe <> Maybe) A) →
                   mapF 𝑀aybe f (multMaybeMorp x) ≡ multMaybeMorp (mapF (𝑀aybe ∙ 𝑀aybe) f x)
  multMaybeAxNat f nothing = refl
  multMaybeAxNat f (just x) = refl

  multMaybe : (𝑀aybe ∙ 𝑀aybe) ~> 𝑀aybe
  multMaybe = NT multMaybeMorp multMaybeAxNat

  axUnitLeftMaybe : {A : Set} → (x : (Id <> Maybe) A) →
                    mor (multMaybe ⊙ (unitMaybe ◁ 𝑀aybe)) x ≡ mor {𝔾 = 𝑀aybe} 𝕦Left x
  axUnitLeftMaybe nothing = refl
  axUnitLeftMaybe (just x) = refl

  axUnitRightMaybe : {A : Set} → (x : (Maybe <> Id) A) →
                     mor (multMaybe ⊙ (𝑀aybe ▷ unitMaybe)) x ≡ mor {𝔾 = 𝑀aybe} 𝕦Right x
  axUnitRightMaybe nothing = refl
  axUnitRightMaybe (just x) = refl

  axAssocMaybe : {A : Set} → (x : ((Maybe <> Maybe) <> Maybe) A) →
                 mor (multMaybe ⊙ (multMaybe ◁ 𝑀aybe)) x ≡ mor (multMaybe ⊙ (𝑀aybe ▷ multMaybe)) x
  axAssocMaybe nothing = refl
  axAssocMaybe (just nothing) = refl
  axAssocMaybe (just (just nothing)) = refl
  axAssocMaybe (just (just (just x))) = refl

  𝕄aybe : Monad Maybe
  𝕄aybe = monad 𝑀aybe unitMaybe multMaybe axUnitLeftMaybe axUnitRightMaybe axAssocMaybe
