module Halogen.ColorPicker.Common where

import Prelude

import Color as C
import Control.Monad.Eff.Class (class MonadEff)
import Control.MonadZero (guard)
import DOM (DOM)
import DOM.HTML (window)
import DOM.HTML.Indexed as I
import DOM.HTML.Types (ALERT)
import DOM.HTML.Window (alert)
import Data.Codec (BasicCodec, basicCodec, bihoistGCodec, decode, encode, hoistCodec, mapCodec, (<~<), (>~>))
import Data.Const (Const)
import Data.Foldable (for_)
import Data.Foreign (readNumber)
import Data.Int as Int
import Data.Int as Number
import Data.Lens (Iso', Lens, Iso, iso, lens, over, review, view, withIso)
import Data.Maybe (Maybe(..))
import Data.Maybe as M
import Data.Maybe.Last (Last(..))
import Data.Newtype (class Newtype, un)
import Data.Record as Rec
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (SProxy(..), Variant, expand, inj, match, on, onMatch)
import Global as G
import Halogen (liftEff)
import Halogen as H
import Halogen.Component.Proxy as HCP
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Unsafe.Coerce (unsafeCoerce)

type ColorModifier m = HCP.ProxyComponent (Const Void) C.Color C.Color m

type ColorModifierQ = HCP.ProxyQ (Const Void) C.Color C.Color

type InputState = InputStateF String

type InputStateF a =
  { input ∷ a
  , color ∷ C.Color
  }

data InputQuery a
  = Receive C.Color a
  | Update String a
  | Blur a

type InputDSL m = H.ComponentDSL InputState InputQuery C.Color m
type InputHTML = H.ComponentHTML InputQuery

type InputProps = Array (HP.IProp I.HTMLinput (InputQuery Unit))

type AlertM err = Tuple (Last err)
type InputC err i o = BasicCodec (AlertM err) i o

type InputBijection  = Iso' C.Color (InputStateF String)
type InputCodec = forall r. InputC (NumErr r) (InputStateF String) C.Color

newtype Number0_255 = Number0_255 Number
derive instance newtypeNumber0_255 :: Newtype Number0_255 _

newtype Number0_100 = Number0_100 Number
derive instance newtypeNumber0_100 :: Newtype Number0_100 _

newtype Number0_1 = Number0_1 Number
derive instance newtypeNumber0_1 :: Newtype Number0_1 _

range0_1 :: Range
range0_1 = { min: 0.0, max: 1.0 }

range0_255 :: Range
range0_255 = { min: 0.0, max: 255.0 }

range0_100 :: Range
range0_100 = { min: 0.0, max: 100.0 }


type Range = { min :: Number, max :: Number }
type NumErrR r = (invalidEntry :: Range, outOfRange :: Range | r)
type NumErr r = Variant (NumErrR r)

showErr :: NumErr () -> String
showErr = match
  { invalidEntry: \{ min, max } ->
    "Invalid numeric entry. A number between " <> show min 
    <> " and " <> show max <> "is required. 0.0 was insered."
    -- TODO try to insert old value and change last part to `Previous value inserted`
  , outOfRange: \{ min, max } -> "A number between " <> show min 
    <> " and " <> show max <> "is required. Closest value insered."
  }

cStrToNum0_1 :: forall r. InputC (NumErr r) String Number0_1
cStrToNum0_1 = addRangeToInvalid range0_1 cStrToNum >~> cNum0_1

cStrToNum0_100 :: forall r. InputC (NumErr r) String Number0_100
cStrToNum0_100 = addRangeToInvalid range0_100 cStrToNum >~> cNum0_100

cStrToNum0_255 :: forall r. InputC (NumErr r) String Number0_255
cStrToNum0_255 = addRangeToInvalid range0_255 cStrToNum >~> cNum0_255


cNum0_1 :: forall r. InputC (NumErr r) Number Number0_1
cNum0_1 = cNumMinMax { range: range0_1, ctr: Number0_1 }

cNum0_100 :: forall r. InputC (NumErr r) Number Number0_100
cNum0_100 = cNumMinMax { range: range0_100, ctr: Number0_100 }

cNum0_255 :: forall r. InputC (NumErr r) Number Number0_255
cNum0_255 = cNumMinMax { range: range0_255, ctr: Number0_255 }

cNumMinMax
  :: forall num err
   . Newtype num Number
  => { range :: Range, ctr :: Number -> num }
  -> InputC (Variant (outOfRange :: Range | err)) Number num
cNumMinMax { range, ctr } = basicCodec dec enc
  where
  dec r =
    if r > range.max
      then Tuple
        (Last $ Just $ inj (SProxy :: SProxy "outOfRange") range)
        (ctr range.max)
    else if r < range.min
      then Tuple
        (Last $ Just $ inj (SProxy :: SProxy "outOfRange") range)
        (ctr range.min)
    else Tuple
      (Last Nothing)
      (ctr r)
  enc = un ctr


cStrToNum :: forall err. InputC (Variant (invalidEntry :: Unit | err)) String Number
cStrToNum = basicCodec dec enc
  where
  dec s =
    let r = G.readFloat s
    in if G.isNaN r
      then Tuple (Last $ Just $ inj (SProxy :: SProxy "invalidEntry") unit) 0.0
      else Tuple (Last Nothing) r
  enc :: Number -> String
  enc = show


mapAlertMErr :: forall a b. (a -> b) -> AlertM a ~> AlertM b
mapAlertMErr f (Tuple (Last err) a) = Tuple (Last $ f <$> err ) a

addRangeToInvalid
  :: forall a b err
  . Range
  -> InputC (Variant (invalidEntry :: Unit |err)) a b
  -> InputC (Variant (invalidEntry :: Range |err)) a b
addRangeToInvalid range =
  hoistCodec (mapAlertMErr $ mapLabel (SProxy :: SProxy "invalidEntry") (const range))

mapLabel :: forall trash a b sym rIn rOut rBase
   . IsSymbol sym
  => RowCons sym a rBase rIn
  => RowCons sym b rBase rOut
  => SProxy sym
  -> (a -> b)
  -> Variant rIn
  -> Variant rOut
mapLabel p f r = on p (inj p <<< f) (unsafeCoerce :: Variant rBase -> Variant rOut) r

hslaEq ∷ C.Color -> C.Color -> Boolean
hslaEq a b = C.toHSLA a `Rec.equal` C.toHSLA b

eval
  ∷ ∀ m eff
  . MonadEff (dom ∷ DOM, alert ∷ ALERT | eff ) m
  ⇒ InputCodec
  → InputQuery
  ~> InputDSL m
eval cdc = case _ of
  Receive c next → do
    st ← H.get
    unless (st.color `hslaEq` c) $ H.put $ encode cdc c
    pure next
  Blur next → do
    st ← H.get
    let (Tuple (Last mbErr) newColor) = decode cdc st
    for_ mbErr $ \err -> do
      liftEff $ window >>= alert (showErr err)
      H.put $ encode cdc newColor
    pure next
  Update s next → do
    H.modify (_{ input = s })
    st ← H.get
    let (Tuple _ newColor) = decode cdc st
    unless (st.color `hslaEq` newColor) do
      H.modify (_{ color = newColor })
      H.raise newColor
    pure next


_Alpha ∷ InputBijection
_Alpha = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.a $ C.toHSLA color }
  mkColor { input, color } =
    let v = G.readFloat input
    in if G.isNaN v || v < 0.0 || v > 1.0 then color
       else let hsla = C.toHSLA color
            in C.hsla hsla.h hsla.s hsla.l v

_Blue ∷ InputBijection
_Blue = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.b $ C.toRGBA color }
  mkColor { input, color } = M.fromMaybe color do
    v ← Int.fromString input
    guard $ v < 256 && v > -1
    let rgba = C.toRGBA color
    pure $ C.rgba rgba.r rgba.g v rgba.a

_Green ∷ InputBijection
_Green = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.g $ C.toRGBA color }
  mkColor { input, color } = M.fromMaybe color do
    v ← Int.fromString input
    guard $ v < 256 && v > -1
    let rgba = C.toRGBA color
    pure $ C.rgba rgba.r v rgba.b rgba.a

_Hex ∷ InputBijection
_Hex = iso mkState mkColor
  where
  mkState color = { color, input: C.toHexString color }
  mkColor { input, color } = M.fromMaybe color do
    c ← C.fromHexString input
    let hsla = C.toHSLA c
    let oldA = _.a $ C.toHSLA color
    pure $ C.hsla hsla.h hsla.s hsla.l oldA

_Hue ∷ InputBijection
_Hue = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.h $ C.toHSLA color }
  mkColor { input, color } =
    let v = G.readFloat input
    in if G.isNaN v then color
       else let hsla = C.toHSLA color
            in C.hsla v hsla.s hsla.l hsla.a

-- _Luminosity ∷ InputBijection
-- _Luminosity = _NumStateToStrState >>> _Luminosity'

-- _Luminosity' ∷ InputBijection'
-- _Luminosity' = iso mkState mkColor
--   where
--   mkState color = { color, input: _.l $ C.toHSLA color }
--   mkColor { input, color } =
--     if G.isNaN input || input < 0.0 || input > 1.0 then color
--       else let hsla = C.toHSLA color
--         in C.hsla hsla.h hsla.s input hsla.a


cInputStateStrToNum ∷ forall r. InputC (NumErr r) (InputStateF String) (InputStateF Number0_1)
cInputStateStrToNum = embed cStrToNum0_1 (_.input) (_.input) (_ { input = _}) (_ { input = _})

embed
  :: forall m a b a' b'
  . Functor m
  => BasicCodec m a b
  -> (a' -> a)
  -> (b' -> b)
  -> (a' -> b -> b')
  -> (b' -> a -> a')
  -> BasicCodec m a' b'
embed c view view' update update' = basicCodec dec enc
  where
  dec :: a' -> m b'
  dec a = decode c (view a) <#> update a
  enc :: b' -> a'
  enc a = update' a $ encode c $ view' a



-- cLuminosity' ∷ forall m. Monad m => BasicCodec m (InputStateF String) C.Color
-- cLuminosity' = cInputStateStrToNum <~< cLuminosity

cLuminosity ∷ forall m. Monad m => BasicCodec m (InputStateF Number0_1) C.Color
cLuminosity = basicCodec dec enc
  where
  enc color = { color, input: Number0_1 $ _.l $ C.toHSLA color }
  dec { input, color } =
    let hsla = C.toHSLA color
    in pure $ C.hsla hsla.h hsla.s (un Number0_1 input) hsla.a
        

_Red ∷ InputBijection
_Red = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.r $ C.toRGBA color }
  mkColor { input, color } = M.fromMaybe color do
    v ← Int.fromString input
    guard $ v < 256 && v > -1
    let rgba = C.toRGBA color
    pure $ C.rgba v rgba.g rgba.b rgba.a

_SaturationHSL ∷ InputBijection
_SaturationHSL = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.s $ C.toHSLA color }
  mkColor { input, color } =
    let v = G.readFloat input
    in if G.isNaN v || v < 0.0 || v > 1.0 then color
       else let hsla = C.toHSLA color
            in C.hsla hsla.h v hsla.l hsla.a

_SaturationHSV ∷ InputBijection
_SaturationHSV = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.s $ C.toHSVA color }
  mkColor { input, color } =
    let v = G.readFloat input
    in if G.isNaN v || v < 0.0 || v > 1.0 then color
       else let hsva = C.toHSVA color
            in C.hsva hsva.h v hsva.v hsva.a

_Value ∷ InputBijection
_Value = iso mkState mkColor
  where
  mkState color = { color, input: show $ _.v $ C.toHSVA color }
  mkColor { input, color } =
    let v = G.readFloat input
    in if G.isNaN v || v < 0.0 || v > 1.0 then color
       else let hsva = C.toHSVA color
            in C.hsva hsva.h hsva.s v hsva.a


inputComponent
  ∷ ∀ m eff
  . MonadEff (dom ∷ DOM, alert ∷ ALERT | eff ) m
  ⇒ InputCodec
  → (InputState → InputHTML)
  → ColorModifier m
inputComponent cdc render = HCP.proxy $ H.component
  { initialState: encode cdc
  , render
  , eval: eval cdc
  , receiver: HE.input Receive
  }
