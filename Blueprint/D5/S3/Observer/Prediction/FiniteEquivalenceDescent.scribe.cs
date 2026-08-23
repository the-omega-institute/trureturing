using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class FiniteEquivalenceDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula RelationAt(Formula index) => new Formula.Subscript(F.Id("R"), index);
        Formula Cardinality(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
        Formula Apply(Formula function, Formula argument) => Seq(function, Open, argument, Close);
        Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
        Formula Relates(Formula relation, Formula left, Formula right) =>
            Seq(relation, Open, left, Comma, Sp, right, Close);

        Formula state = F.Id("Y");
        Formula relation = F.Id("R");
        Formula update = Tau;
        Formula index = F.Id("m");
        Formula otherIndex = F.Id("n");
        Formula iterateIndex = F.Id("k");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula zeroRelation = RelationAt(D(0));
        Formula finiteRelation = RelationAt(index);
        Formula successorRelation = RelationAt(Seq(index, Plus, D(1)));
        Formula otherRelation = RelationAt(otherIndex);
        Formula otherSuccessor = RelationAt(Seq(otherIndex, Plus, D(1)));
        Formula depth = new Formula.Subscript(F.Id("m"), relation);
        Formula stableRelation = RelationAt(depth);
        Formula stableSuccessor = RelationAt(Seq(depth, Plus, D(1)));
        Formula core = Seq(new Formula.Subscript(F.Id("C"), update), Open, relation, Close);
        Formula quotient = Seq(state, Slash, relation);
        Formula coreQuotient = Seq(state, Slash, core);
        Formula updatePower = Seq(update, Caret, Grp(iterateIndex));
        Formula iteratedLeft = Apply(updatePower, left);
        Formula iteratedRight = Apply(updatePower, right);
        Formula finiteSet = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Forall, Sp, iterateIndex, Comma, Sp,
            iterateIndex, Sp, Leq, Sp, index, Sp, Rightarrow, Sp,
            Relates(relation, iteratedLeft, iteratedRight), CloseBrace);
        Formula coreSet = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Forall, Sp, iterateIndex, Comma, Sp,
            Relates(relation, iteratedLeft, iteratedRight), CloseBrace);
        Formula successorSet = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Relates(relation, left, right), Sp, Land, Sp,
            Relates(finiteRelation, Apply(update, left), Apply(update, right)), CloseBrace);
        Formula stableTest = Seq(
            OpenBrace, index, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp, Mid, Sp,
            finiteRelation, Sp, Eq, Sp, successorRelation, CloseBrace);
        Formula depthDefinition = Seq(
            depth, Sp, Eq, Sp, Operatorname, Grp(F.Id("sInf")), Sp, stableTest);

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, state, Close, CloseBracket, Comma, Sp,
            relation, Colon, Sp, Operatorname, Grp(F.Id("Setoid")),
            Open, state, Close, Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, RowBreak, Grp(),
            zeroRelation, Sp, Eq, Sp, relation, Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            successorRelation, Sp, Eq, Sp, successorSet, Close, Sp, Land, Sp,
            RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            finiteRelation, Sp, Eq, Sp, finiteSet, Close, Sp, Land, Sp,
            RowBreak, Grp(),
            core, Sp, Eq, Sp, coreSet, Sp, Land, Sp, RowBreak, Grp(),
            depthDefinition, Sp, Land, Sp, stableRelation, Sp, Eq, Sp,
            stableSuccessor, Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, otherIndex, Comma, Sp,
            otherRelation, Sp, Eq, Sp, otherSuccessor, Sp, Rightarrow, Sp,
            depth, Sp, Leq, Sp, otherIndex, Close, Sp, Land, Sp,
            RowBreak, Grp(),
            Open, Forall, Sp, otherIndex, Comma, Sp,
            depth, Sp, Leq, Sp, otherIndex, Sp, Rightarrow, Sp,
            otherRelation, Sp, Eq, Sp, core, Close, Sp, Land, Sp,
            RowBreak, Grp(),
            depth, Sp, Leq, Sp,
            Cardinality(coreQuotient), Sp, Minus, Sp, Cardinality(quotient),
            Sp, Leq, Sp,
            Cardinality(state), Sp, Minus, Sp, Cardinality(quotient), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite equivalence refinement stabilizes within its quotient-class budget.",
            H("Finite Equivalence Descent"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-equivalence-descent-and-stability-bound"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/Prediction/FiniteEquivalenceDescent."
                            + "finite_equivalence_descent_and_stability_bound"),
                    H("Finite descent and general stability bound"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let Y be a finite carrier, R an equivalence relation, and tau its "
                                + "deterministic update. The canonical readout sends each state "
                                + "to its R-class. Equality of finite readout words then constructs "
                                + "the source sequence directly from R and iterates of tau.")),
                        Paragraph(Text(
                            "The zero and successor clauses identify this sequence with repeated "
                                + "intersection by the one-step pullback. The finite-intersection "
                                + "formula states equivalently that two states remain related at "
                                + "every iterate from zero through the chosen depth.")),
                        Paragraph(Text(
                            "The displayed depth is the least index where consecutive finite "
                                + "relations agree. At that depth and every later one, the relation "
                                + "is the canonical all-future core.")),
                        Paragraph(Text(
                            "The terminal quotient can gain at most one unit of stability depth "
                                + "per new class. This gives the sharp difference between terminal "
                                + "and initial quotient counts, followed by the carrier bound. The "
                                + "empty finite carrier is included and handled directly."))),
                    DescribeRole.Theorem))));
    }
}
