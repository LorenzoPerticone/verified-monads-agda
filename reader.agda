module reader where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils
  open import definitions

  Reader : Set → Set → Set
  Reader E A = E → A

  infixl 20 _$_
  _$_ : {A B : Set} → Reader A B → A → B
  f $ x = f x

  mapReader : {A B E : Set} → (A → B) →
              Reader E A → Reader E B
  mapReader f x = f ∘ x

  mapReplaceReader : {A B E : Set} →
                     (f : A → B) → (g : A → B) →
                     ((x : A) → f x ≡ g x) →
                     (y : Reader E A) → mapReader f y ≡ mapReader g y
  mapReplaceReader f g p y = {!!}

  ax1Reader : {A E : Set} → (x : Reader E A) →
              mapReader id x ≡ x
  ax1Reader x = refl

  ax2Reader : {A B C E : Set} →
              (f : B → C) → (g : A → B) →
              (x : Reader E A) →
              mapReader (f ∘ g) x ≡ mapReader f (mapReader g x)
  ax2Reader f g x = refl

  𝑅eader : (E : Set) → Functor (Reader E)
  𝑅eader E = functor mapReader mapReplaceReader ax1Reader ax2Reader

  unitReaderMorp : {A E : Set} → Id A → Reader E A
  unitReaderMorp x = λ _ → x

  unitReaderAxNat : {A B E : Set} →
                    (f : A → B) →
                    (x : Id A) →
                    mapReader {E = E} f (unitReaderMorp x) ≡ unitReaderMorp (id f x)
  unitReaderAxNat f x = refl

  unitReader : {E : Set} → 𝟙 ~> 𝑅eader E
  unitReader = NT unitReaderMorp unitReaderAxNat

  multReaderMorp : {A E : Set} →
                   (Reader E <> Reader E) A → Reader E A
  multReaderMorp f = λ x → f x x

  multReaderAxNat : {A B E : Set} →
                    (f : A → B) →
                    (x : (Reader E <> Reader E) A) →
                    mapReader f (multReaderMorp x) ≡ multReaderMorp (mapReader (mapReader f) x)
  multReaderAxNat f x = refl

  multReader : {E : Set} → (𝑅eader E ∙ 𝑅eader E) ~> 𝑅eader E
  multReader = NT multReaderMorp multReaderAxNat

  axUnitLeftReader : {A E : Set} → (x : (Id <> Reader E) A) →
                     mor (multReader ⊙ (unitReader ◁ 𝑅eader E)) x ≡ mor {𝔾 = 𝑅eader E} 𝕦Left x
  axUnitLeftReader x = refl

  axUnitRightReader : {A E : Set} → (x : (Reader E <> Id) A) →
                      mor (multReader ⊙ (𝑅eader E ▷ unitReader)) x ≡ mor {𝔾 = 𝑅eader E} 𝕦Right x
  axUnitRightReader x = refl

  axAssocReader : {A E : Set} → (x : (Reader E <> Reader E <> Reader E) A) →
                  multReaderMorp (multReaderMorp x) ≡
                  multReaderMorp (mapReader multReaderMorp x)
  axAssocReader x = refl

  ℝeader : (E : Set) → Monad (Reader E)
  ℝeader E = monad (𝑅eader E) unitReader multReader axUnitLeftReader axUnitRightReader axAssocReader
