module either where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils
  open import definitions

  data Either (E : Set) : Set → Set where
    left : {A : Set} → E → Either E A
    right : {A : Set} → A → Either E A

  choice : {A B E : Set} →
           Either A E → (A → B) → (E → B) → B
  choice (left x) f _ = f x
  choice (right y) _ g = g y

  mapEither : {A B E : Set} → (A → B) → Either E A → Either E B
  mapEither f (left x) = left x
  mapEither f (right x) = right (f x)

  mapReplaceEither : {A B E : Set} →
                     (f : A → B) → (g : A → B) →
                     ((x : A) → f x ≡ g x) →
                     (y : Either E A) →
                     mapEither f y ≡ mapEither g y
  mapReplaceEither f g p (left x) = refl
  mapReplaceEither f g p (right x) = cong right (p x)

  ax1Either : {A E : Set} → (x : Either E A) →
              mapEither id x ≡ x
  ax1Either (left x) = refl
  ax1Either (right x) = refl

  ax2Either : {A B C E : Set} → (f : B → C) → (g : A → B) → (x : Either E A) →
              mapEither (f ∘ g) x ≡ mapEither f (mapEither g x)
  ax2Either f g (left x) = refl
  ax2Either f g (right x) = refl

  𝐸ither : (E : Set) → Functor (Either E)
  𝐸ither E = functor mapEither mapReplaceEither ax1Either ax2Either

  unitEitherMorp : {A E : Set} → Id A → Either E A
  unitEitherMorp x = right x

  unitEitherAxNat : {A B E : Set} → (f : A → B) → (x : Id A) →
                    mapEither {E = E} f (unitEitherMorp x) ≡ unitEitherMorp (mapF 𝟙 f x)
  unitEitherAxNat f x = refl

  unitEither : {E : Set} → 𝟙 ~> 𝐸ither E
  unitEither = NT unitEitherMorp unitEitherAxNat

  multEitherMorp : {A E : Set} → (Either E <> Either E) A → Either E A
  multEitherMorp (left x) = left x
  multEitherMorp (right (left x)) = left x
  multEitherMorp (right (right x)) = right x

  multEitherAxNat : {A B E : Set} → (f : A → B) →
                   (x : (Either E <> Either E) A) →
                   mapF (𝐸ither E) f (multEitherMorp x) ≡ multEitherMorp (mapF (𝐸ither E ∙ 𝐸ither E) f x)
  multEitherAxNat f (left x) = refl
  multEitherAxNat f (right (left x)) = refl
  multEitherAxNat f (right (right x)) = refl

  multEither : {E : Set} → ((𝐸ither E) ∙ (𝐸ither E)) ~> (𝐸ither E)
  multEither = NT multEitherMorp multEitherAxNat

  axUnitLeftEither : {A E : Set} → (x : (Id <> Either E) A) →
                     mor (multEither ⊙ (unitEither ◁ 𝐸ither E)) x ≡ mor {𝔾 = 𝐸ither E} 𝕦Left x
  axUnitLeftEither (left x) = refl
  axUnitLeftEither (right x) = refl

  axUnitRightEither : {A E : Set} → (x : (Either E <> Id) A) →
                      mor (multEither ⊙ (𝐸ither E ▷ unitEither)) x ≡ mor {𝔾 = 𝐸ither E} 𝕦Right x
  axUnitRightEither (left x) = refl
  axUnitRightEither (right x) = refl

  axAssocEither : {A E : Set} → (x : (Either E <> Either E <> Either E) A) →
                  mor (multEither ⊙ (multEither ◁ 𝐸ither E)) x ≡
                  mor (multEither ⊙ (𝐸ither E ▷ multEither)) x
  axAssocEither (left x) = refl
  axAssocEither (right (left x)) = refl
  axAssocEither (right (right (left x))) = refl
  axAssocEither (right (right (right x))) = refl

  𝔼ither : (E : Set) → Monad (Either E)
  𝔼ither E = monad (𝐸ither E) unitEither multEither axUnitLeftEither axUnitRightEither axAssocEither

