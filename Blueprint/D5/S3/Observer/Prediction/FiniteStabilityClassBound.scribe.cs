using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Prediction;

internal sealed class FiniteStabilityClassBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula Cardinality(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
        Formula RelationAt(Formula index) => new Formula.Subscript(F.Id("K"), index);

        Formula state = F.Id("X");
        Formula output = F.Id("Q");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula index = F.Id("n");
        Formula depth = new Formula.Subscript(F.Id("m"), Star);
        Formula finiteRelation = RelationAt(index);
        Formula nextRelation = RelationAt(Seq(index, Plus, D(1)));
        Formula stableRelation = RelationAt(depth);
        Formula stableNext = RelationAt(Seq(depth, Plus, D(1)));
        Formula completeRelation = RelationAt(Infty);
        Formula stableIndices = Seq(
            OpenBrace, index, InMacro, Mathbb, Grp(F.Id("N")), Sp, Mid, Sp,
            finiteRelation, Sp, Eq, Sp, nextRelation, CloseBrace);
        Formula completionQuotient = Seq(state, Slash, completeRelation);
        Formula initialQuotient = Seq(state, Slash, RelationAt(readout));
        Formula image = Seq(Operatorname, Grp(F.Id("Im")), Open, readout, Close);

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma,
            RowBreak, Grp(),
            depth, Sp, Eq, Sp, Operatorname, Grp(F.Id("sInf")), Sp,
            stableIndices, Comma, RowBreak, Grp(),
            stableRelation, Sp, Eq, Sp, stableNext, Sp, Eq, Sp,
            completeRelation, Sp, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            finiteRelation, Sp, Eq, Sp, nextRelation, Sp, Rightarrow, Sp,
            depth, Sp, Leq, Sp, index, Close, Sp, Land, Sp,
            RowBreak, Grp(),
            depth, Sp, Leq, Sp,
            Cardinality(completionQuotient), Sp, Minus, Sp,
            Cardinality(initialQuotient), Sp, Leq, Sp,
            Cardinality(state), Sp, Minus, Sp, Cardinality(image), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The least finite-future stability depth obeys the exact quotient-class bound.",
            H("Finite Stability Class Bound"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-stability-class-bound"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/Prediction/FiniteStabilityClassBound."
                            + "finite_stability_class_bound"),
                    H("Least finite-future stability depth"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let X be a finite state carrier, let F be its deterministic update, "
                                + "and let q be an arbitrary readout. The relation K_n identifies "
                                + "states with equal readouts from time zero through time n, while "
                                + "K_infinity identifies states with equal readouts at every time.")),
                        Paragraph(Text(
                            "The displayed depth is the canonical least index where two adjacent "
                                + "finite-future relations agree. At that depth both adjacent "
                                + "relations equal the complete-future relation, and the quantified "
                                + "clause states minimality directly.")),
                        Paragraph(Text(
                            "Each strict refinement creates at least one new quotient class. The "
                                + "resulting depth is therefore bounded by the difference between "
                                + "the complete-future and current-readout quotients; the canonical "
                                + "kernel-quotient equivalence identifies the latter with the "
                                + "realized image of q."))),
                    DescribeRole.Theorem))));
    }
}
