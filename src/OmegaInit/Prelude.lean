module
public import Init.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Add And AndOp AndThen Append Applicative Array Array.appendCore.loop Array.appendCore.loop.match_1 Array.extract.loop BEq Bind BitVec BitVec.decEq.match_1 Bool Bool.Reflects.match_1 Bool.false.elim Bool.true.elim ByteArray ByteArray.push.match_1 ByteArray.size.match_1 Char Char.mk.noConfusion Complement Decidable DecidableEq DecidableRel Div EStateM EStateM.Backtrackable EStateM.Result EStateM.Result.error.elim EStateM.Result.ok.elim EStateM.adaptExcept EStateM.adaptExcept.match_1 EStateM.bind EStateM.bind.match_1 EStateM.dummyRestore EStateM.dummySave EStateM.get EStateM.instInhabited EStateM.instInhabitedResult EStateM.instMonad EStateM.instMonadExceptOfOfBacktrackable EStateM.instMonadStateOf EStateM.instOrElseOfBacktrackable EStateM.map EStateM.modifyGet EStateM.modifyGet.match_1 EStateM.nonBacktrackable EStateM.orElse EStateM.pure EStateM.run EStateM.run' EStateM.seqRight EStateM.set EStateM.throw EStateM.tryCatch EStateM.tryCatch.match_1 Empty Eq Except Except.error.elim Except.ok.elim False Fin Functor HAdd HAnd HAndThen HAppend HDiv HEq HMod HMul HOr HOrElse HPow HSMul HShiftLeft HShiftRight HSub HXor HomogeneousPow Inhabited LE LT List List.append.match_1 List.beq.match_1 List.brecOn.go List.concat.match_1 List.cons.elim List.foldl.match_1 List.get.match_1 List.hasDecEq.go List.hasDecEq.go.match_1 List.hasDecEq.go.match_3 List.lengthTRAux.match_1 List.nil.elim List.set.match_1 List.toByteArray.loop List.toByteArray.match_1 MProd Max Membership Min Mod Monad MonadEval MonadEvalT MonadExcept MonadExcept.ofExcept.match_1 MonadExceptOf MonadFunctor MonadFunctorT MonadLift MonadLiftT MonadReader MonadReaderOf MonadState MonadStateOf MonadWithReader MonadWithReaderOf Mul Nat Nat.add.match_1 Nat.beq.match_1 Nat.ble.match_1 Nat.brecOn.eq Nat.brecOn.go Nat.decEq.match_1 Nat.div.go.match_1 Nat.modCore.go Nat.mul.match_1 Nat.pow.match_1 Nat.succ.elim Nat.zero.elim NatPow Nonempty NonemptyType Not OfNat Option Option.none.elim Option.some.elim Or OrElse OrOp PEmpty PLift PLift.up.noConfusion PProd PULift PUnit Pow Prod Pure Quot Quot.ind Quot.lift Quot.liftOn Quot.mk ReaderT ReaderT.adapt ReaderT.bind ReaderT.instApplicativeOfMonad ReaderT.instFunctorOfMonad ReaderT.instMonad ReaderT.instMonadExceptOf ReaderT.instMonadFunctor ReaderT.instMonadLift ReaderT.mk ReaderT.pure ReaderT.read ReaderT.run SMul Seq SeqLeft SeqRight ShiftLeft ShiftRight String String.Pos.Raw.mk.noConfusion Sub Subtype Trans True UInt16 UInt16.decEq.match_1 UInt32 UInt32.decEq.match_1 UInt64 UInt64.decEq.match_1 UInt8 UInt8.decEq.match_1 ULift ULift.up.noConfusion Unit Unit.unit XorOp absurd cast cond cond.match_1 congr congrArg congrFun congrFun' decEq decide_eq_false dite eq_of_heq getModify getThe heq_of_eq id id_eq inferInstance instAddNat instBEqOfDecidableEq instDecidableAnd instDecidableEqBitVec instDecidableEqBool instDecidableEqChar instDecidableEqChar.match_1 instDecidableEqFin instDecidableEqFin.match_1 instDecidableEqList instDecidableEqList.match_1 instDecidableEqList.match_3 instDecidableEqList.match_5 instDecidableEqNat instDecidableEqUInt16 instDecidableEqUInt32 instDecidableEqUInt64 instDecidableEqUInt8 instDecidableLeBitVec instDecidableLtBitVec instDecidableOr instDecidableOr.match_1 instDecidableOr.match_3 instHAdd instHAndOfAndOp instHAndThenOfAndThen instHAppendOfAppend instHDiv instHMod instHMul instHOrElseOfOrElse instHOrOfOrOp instHPow instHSMul instHShiftLeftOfShiftLeft instHShiftRightOfShiftRight instHSub instHXorOfXorOp instInhabitedBool instInhabitedBool.default instInhabitedExcept instInhabitedForall instInhabitedForallOfMonad instInhabitedList instInhabitedNat instInhabitedNonemptyType instInhabitedOfMonad instInhabitedOption instInhabitedReaderT instInhabitedSort instInhabitedULift instLEBitVec instLEFin instLENat instLEUInt32 instLEUInt8 instLTBitVec instLTFin instLTNat instLTUInt32 instLTUInt8 instMaxUInt32 instMinNat instMinUInt32 instMonadEvalOfMonadLift instMonadEvalT instMonadEvalTOfMonadEval instMonadExceptOfMonadExceptOf instMonadFunctorTOfMonadFunctor instMonadLiftT instMonadLiftTOfMonadLift instMonadReaderOfMonadReaderOf instMonadReaderOfOfMonadLift instMonadReaderOfReaderTOfMonad instMonadStateOfMonadStateOf instMonadStateOfOfMonadLift instMonadWithReaderOfMonadWithReaderOf instMonadWithReaderOfOfMonadFunctor instMonadWithReaderOfReaderT instMulNat instNatPowNat instOfNatNat instPowNat instPowOfHomogeneousPow instSMulOfMul instSubNat ite liftM maxOfLe minOfLe modify modifyGetThe modifyThe monadFunctorRefl namedPattern noConfusion_of_Nat of_decide_eq_true optParam outParam readThe rfl semiOutParam throwThe tryCatchThe withTheReader «inferInstanceAs»)
end Omega
namespace Omega.Add
export _root_.Add (add mk rec)
end Omega.Add
namespace Omega.And
export _root_.And (casesOn intro left rec recOn right)
end Omega.And
namespace Omega.AndOp
export _root_.AndOp (and casesOn mk rec recOn)
end Omega.AndOp
namespace Omega.AndThen
export _root_.AndThen (andThen casesOn mk rec recOn)
end Omega.AndThen
namespace Omega.Append
export _root_.Append (append casesOn mk rec recOn)
end Omega.Append
namespace Omega.Applicative
export _root_.Applicative (casesOn mk rec recOn toFunctor toPure toSeq toSeqLeft toSeqRight)
end Omega.Applicative
namespace Omega.Array
export _root_.Array (appendCore casesOn empty emptyWithCapacity extract getD getInternal mk mkArray0 mkArray1 mkArray2 mkArray3 mkArray4 mkArray5 mkArray6 mkArray7 mkArray8 mkEmpty push rec recOn size toList)
end Omega.Array
namespace Omega.BEq
export _root_.BEq (beq casesOn mk rec recOn)
end Omega.BEq
namespace Omega.Bind
export _root_.Bind (bind casesOn mk rec recOn)
end Omega.Bind
namespace Omega.BitVec
export _root_.BitVec (casesOn decEq noConfusion noConfusionType ofFin ofNat ofNatLT rec recOn toFin toNat)
end Omega.BitVec
namespace Omega.Bool
export _root_.Bool (Reflects and and_eq_internalAnd beq casesOn ctorElim ctorElimType ctorIdx dcond decEq eq_false_of_ne_true eq_true_of_ne_false false ne_false_of_eq_true ne_true_of_eq_false noConfusion noConfusionType not not_eq_internalNot or or_eq_internalOr rec true)
end Omega.Bool
namespace Omega.Bool.Internal
export _root_.Bool.Internal (and not or)
end Omega.Bool.Internal
namespace Omega.ByteArray
export _root_.ByteArray (IsValidUTF8 casesOn data empty emptyWithCapacity mk push rec recOn size)
end Omega.ByteArray
namespace Omega.ByteArray.IsValidUTF8
export _root_.ByteArray.IsValidUTF8 (casesOn intro rec recOn)
end Omega.ByteArray.IsValidUTF8
namespace Omega.Char
export _root_.Char (casesOn ctorIdx ext mk ne_of_val_ne noConfusion noConfusionType ofNat ofNatAux rec recOn utf8Size val val_eq_of_eq val_ne_of_ne valid)
end Omega.Char
namespace Omega.Complement
export _root_.Complement (casesOn complement mk rec recOn)
end Omega.Complement
namespace Omega.Decidable
export _root_.Decidable (casesOn decide falseTrueCases intro isFalse isTrue rec reflects_decide)
end Omega.Decidable
namespace Omega.Div
export _root_.Div (casesOn div mk rec recOn)
end Omega.Div
namespace Omega.EStateM.Backtrackable
export _root_.EStateM.Backtrackable (casesOn mk rec recOn restore save)
end Omega.EStateM.Backtrackable
namespace Omega.EStateM.Result
export _root_.EStateM.Result (casesOn ctorElim ctorElimType ctorIdx error ok rec recOn)
end Omega.EStateM.Result
namespace Omega.Empty
export _root_.Empty (casesOn noConfusion noConfusionType rec recOn)
end Omega.Empty
namespace Omega.Eq
export _root_.Eq (casesOn ndrec ndrec_symm rec recOn refl subst symm trans)
end Omega.Eq
namespace Omega.Except
export _root_.Except (casesOn ctorElim ctorElimType ctorIdx error ok rec recOn)
end Omega.Except
namespace Omega.False
export _root_.False (casesOn elim rec)
end Omega.False
namespace Omega.Fin
export _root_.Fin (casesOn decLe decLt eq_of_val_eq isLt mk rec recOn val val_eq_of_eq)
end Omega.Fin
namespace Omega.Fin.Internal
export _root_.Fin.Internal (ofNat)
end Omega.Fin.Internal
namespace Omega.Function
export _root_.Function (comp const)
end Omega.Function
namespace Omega.Functor
export _root_.Functor (casesOn map mapConst mk rec recOn)
end Omega.Functor
namespace Omega.GE
export _root_.GE (ge)
end Omega.GE
namespace Omega.GT
export _root_.GT (gt)
end Omega.GT
namespace Omega.HAdd
export _root_.HAdd (hAdd mk rec)
end Omega.HAdd
namespace Omega.HAnd
export _root_.HAnd (casesOn hAnd mk rec recOn)
end Omega.HAnd
namespace Omega.HAndThen
export _root_.HAndThen (casesOn hAndThen mk rec recOn)
end Omega.HAndThen
namespace Omega.HAppend
export _root_.HAppend (casesOn hAppend mk rec recOn)
end Omega.HAppend
namespace Omega.HDiv
export _root_.HDiv (casesOn hDiv mk rec recOn)
end Omega.HDiv
namespace Omega.HEq
export _root_.HEq (casesOn rec refl rfl)
end Omega.HEq
namespace Omega.HMod
export _root_.HMod (casesOn hMod mk rec recOn)
end Omega.HMod
namespace Omega.HMul
export _root_.HMul (casesOn hMul mk rec recOn)
end Omega.HMul
namespace Omega.HOr
export _root_.HOr (casesOn hOr mk rec recOn)
end Omega.HOr
namespace Omega.HOrElse
export _root_.HOrElse (casesOn hOrElse mk rec recOn)
end Omega.HOrElse
namespace Omega.HPow
export _root_.HPow (casesOn hPow mk rec recOn)
end Omega.HPow
namespace Omega.HSMul
export _root_.HSMul (casesOn hSMul mk rec recOn)
end Omega.HSMul
namespace Omega.HShiftLeft
export _root_.HShiftLeft (casesOn hShiftLeft mk rec recOn)
end Omega.HShiftLeft
namespace Omega.HShiftRight
export _root_.HShiftRight (casesOn hShiftRight mk rec recOn)
end Omega.HShiftRight
namespace Omega.HSub
export _root_.HSub (casesOn hSub mk rec recOn)
end Omega.HSub
namespace Omega.HXor
export _root_.HXor (casesOn hXor mk rec recOn)
end Omega.HXor
namespace Omega.HomogeneousPow
export _root_.HomogeneousPow (casesOn mk pow rec recOn)
end Omega.HomogeneousPow
namespace Omega.Inhabited
export _root_.Inhabited (casesOn default mk rec recOn)
end Omega.Inhabited
namespace Omega.LE
export _root_.LE (casesOn le mk rec recOn)
end Omega.LE
namespace Omega.LT
export _root_.LT (casesOn lt mk rec recOn)
end Omega.LT
namespace Omega.Lean
export _root_.Lean (Name ParserDescr SyntaxNodeKind)
end Omega.Lean
namespace Omega.Lean.Name
export _root_.Lean.Name (anonymous casesOn mkStr1 num rec recOn str)
end Omega.Lean.Name
namespace Omega.Lean.ParserDescr
export _root_.Lean.ParserDescr (binary casesOn cat const node nodeWithAntiquot nonReservedSymbol parser rec recOn sepBy sepBy1 symbol trailingNode unary unicodeSymbol)
end Omega.Lean.ParserDescr
namespace Omega.List
export _root_.List (append below beq brecOn casesOn concat cons ctorElim ctorElimType ctorIdx flatMap flatten foldl get hasDecEq instDecidableEqNil instDecidableNilEq length lengthTR lengthTRAux map nil noConfusion noConfusionType rec recOn set toArray toByteArray utf8Encode)
end Omega.List
namespace Omega.MProd
export _root_.MProd (casesOn fst mk rec recOn snd)
end Omega.MProd
namespace Omega.Max
export _root_.Max (casesOn max mk rec recOn)
end Omega.Max
namespace Omega.Membership
export _root_.Membership (casesOn mem mk rec recOn)
end Omega.Membership
namespace Omega.Min
export _root_.Min (casesOn min mk rec recOn)
end Omega.Min
namespace Omega.Mod
export _root_.Mod (casesOn mk mod rec recOn)
end Omega.Mod
namespace Omega.Monad
export _root_.Monad (casesOn mk rec recOn toApplicative toBind)
end Omega.Monad
namespace Omega.MonadEval
export _root_.MonadEval (casesOn mk monadEval rec recOn)
end Omega.MonadEval
namespace Omega.MonadEvalT
export _root_.MonadEvalT (casesOn mk monadEval rec recOn)
end Omega.MonadEvalT
namespace Omega.MonadExcept
export _root_.MonadExcept (casesOn instOrElse mk ofExcept orElse rec recOn throw tryCatch)
end Omega.MonadExcept
namespace Omega.MonadExceptOf
export _root_.MonadExceptOf (casesOn mk rec recOn throw tryCatch)
end Omega.MonadExceptOf
namespace Omega.MonadFunctor
export _root_.MonadFunctor (casesOn mk monadMap rec recOn)
end Omega.MonadFunctor
namespace Omega.MonadFunctorT
export _root_.MonadFunctorT (casesOn mk monadMap rec recOn)
end Omega.MonadFunctorT
namespace Omega.MonadLift
export _root_.MonadLift (casesOn mk monadLift rec recOn)
end Omega.MonadLift
namespace Omega.MonadLiftT
export _root_.MonadLiftT (casesOn mk monadLift rec recOn)
end Omega.MonadLiftT
namespace Omega.MonadReader
export _root_.MonadReader (casesOn mk read rec recOn)
end Omega.MonadReader
namespace Omega.MonadReaderOf
export _root_.MonadReaderOf (casesOn mk read rec recOn)
end Omega.MonadReaderOf
namespace Omega.MonadState
export _root_.MonadState (casesOn get mk modifyGet rec recOn set)
end Omega.MonadState
namespace Omega.MonadStateOf
export _root_.MonadStateOf (casesOn get mk modifyGet rec recOn set)
end Omega.MonadStateOf
namespace Omega.MonadWithReader
export _root_.MonadWithReader (casesOn mk rec recOn withReader)
end Omega.MonadWithReader
namespace Omega.MonadWithReaderOf
export _root_.MonadWithReaderOf (casesOn mk rec recOn withReader)
end Omega.MonadWithReaderOf
namespace Omega.Mul
export _root_.Mul (casesOn mk mul rec recOn)
end Omega.Mul
namespace Omega.Nat
export _root_.Nat (add add_pos_right below beq ble ble_eq_true_of_le brecOn casesOn ctorElim ctorElimType ctorIdx decEq decLe decLt div div_rec_fuel_lemma div_rec_lemma eq_of_beq_eq_true eq_or_lt_of_le instDiv instMod isValidChar le le_antisymm le_of_ble_eq_true le_of_lt_succ le_of_succ_le_succ le_refl le_succ le_succ_of_le le_trans lt lt_add_one lt_irrefl lt_of_lt_of_le lt_of_not_le lt_or_ge lt_succ_of_le lt_succ_self lt_trans mod modCore modCoreGo_lt modCore_lt mod_lt mul mul_pos ne_of_beq_eq_false noConfusion noConfusionType not_lt_zero not_succ_le_zero pow pow_pos pred pred_le rec recOn sub sub_le sub_lt succ succ_le_succ succ_sub_succ_eq_sub zero zero_le zero_lt_succ)
end Omega.Nat
namespace Omega.Nat.le
export _root_.Nat.le (casesOn rec recOn refl step)
end Omega.Nat.le
namespace Omega.NatPow
export _root_.NatPow (casesOn mk pow rec recOn)
end Omega.NatPow
namespace Omega.Nonempty
export _root_.Nonempty (casesOn elim intro rec recOn)
end Omega.Nonempty
namespace Omega.OfNat
export _root_.OfNat (mk ofNat rec)
end Omega.OfNat
namespace Omega.Option
export _root_.Option (casesOn ctorElim ctorElimType ctorIdx getD map noConfusion noConfusionType none rec recOn some)
end Omega.Option
namespace Omega.Or
export _root_.Or (casesOn elim inl inr intro_left intro_right neg_resolve_left neg_resolve_right rec recOn resolve_left resolve_right)
end Omega.Or
namespace Omega.OrElse
export _root_.OrElse (casesOn mk orElse rec recOn)
end Omega.OrElse
namespace Omega.OrOp
export _root_.OrOp (casesOn mk or rec recOn)
end Omega.OrOp
namespace Omega.PEmpty
export _root_.PEmpty (casesOn noConfusion noConfusionType rec recOn)
end Omega.PEmpty
namespace Omega.PLift
export _root_.PLift (casesOn down noConfusion noConfusionType rec recOn up)
end Omega.PLift
namespace Omega.PProd
export _root_.PProd (casesOn fst mk rec snd)
end Omega.PProd
namespace Omega.PULift
export _root_.PULift (casesOn down rec recOn up)
end Omega.PULift
namespace Omega.PUnit
export _root_.PUnit (casesOn rec unit)
end Omega.PUnit
namespace Omega.Pi
export _root_.Pi (instInhabited)
end Omega.Pi
namespace Omega.Pow
export _root_.Pow (casesOn mk pow rec recOn)
end Omega.Pow
namespace Omega.Prod
export _root_.Prod (casesOn fst mk noConfusion noConfusionType rec recOn snd)
end Omega.Prod
namespace Omega.Pure
export _root_.Pure (casesOn mk pure rec recOn)
end Omega.Pure
namespace Omega.SMul
export _root_.SMul (casesOn mk rec recOn smul)
end Omega.SMul
namespace Omega.Seq
export _root_.Seq (casesOn mk rec recOn seq)
end Omega.Seq
namespace Omega.SeqLeft
export _root_.SeqLeft (casesOn mk rec recOn seqLeft)
end Omega.SeqLeft
namespace Omega.SeqRight
export _root_.SeqRight (casesOn mk rec recOn seqRight)
end Omega.SeqRight
namespace Omega.ShiftLeft
export _root_.ShiftLeft (casesOn mk rec recOn shiftLeft)
end Omega.ShiftLeft
namespace Omega.ShiftRight
export _root_.ShiftRight (casesOn mk rec recOn shiftRight)
end Omega.ShiftRight
namespace Omega.String
export _root_.String (casesOn isValidUTF8 ofByteArray ofList rec recOn toByteArray utf8EncodeChar)
end Omega.String
namespace Omega.String.Pos
export _root_.String.Pos (Raw)
end Omega.String.Pos
namespace Omega.String.Pos.Raw
export _root_.String.Pos.Raw (byteIdx casesOn ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.String.Pos.Raw
namespace Omega.Sub
export _root_.Sub (casesOn mk rec recOn sub)
end Omega.Sub
namespace Omega.Subtype
export _root_.Subtype (casesOn mk noConfusion noConfusionType property rec recOn val)
end Omega.Subtype
namespace Omega.Trans
export _root_.Trans (casesOn mk rec recOn trans)
end Omega.Trans
namespace Omega.True
export _root_.True (casesOn intro rec recOn)
end Omega.True
namespace Omega.UInt16
export _root_.UInt16 (casesOn decEq noConfusion noConfusionType ofBitVec rec recOn toBitVec)
end Omega.UInt16
namespace Omega.UInt32
export _root_.UInt32 (casesOn decEq decLe decLt isValidChar noConfusion noConfusionType ofBitVec ofNatLT rec recOn size toBitVec toNat)
end Omega.UInt32
namespace Omega.UInt64
export _root_.UInt64 (casesOn decEq noConfusion noConfusionType ofBitVec rec recOn toBitVec)
end Omega.UInt64
namespace Omega.UInt8
export _root_.UInt8 (casesOn decEq decLe decLt le lt noConfusion noConfusionType ofBitVec ofNat rec recOn toBitVec)
end Omega.UInt8
namespace Omega.ULift
export _root_.ULift (casesOn down noConfusion noConfusionType rec recOn up)
end Omega.ULift
namespace Omega.XorOp
export _root_.XorOp (casesOn mk rec recOn xor)
end Omega.XorOp
