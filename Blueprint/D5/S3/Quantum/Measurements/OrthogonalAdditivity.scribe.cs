using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class OrthogonalAdditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normal positive state is additive on a complete orthogonal projection family.",
        H("Orthogonal Additivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normal-state-orthogonal-additivity-and-parseval"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurements/OrthogonalAdditivity.orthogonal_additivity"),
                H("Normal-state additivity and pure-state Parseval decomposition"),
                StatementSource.FromAuthor(AdditivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be a unital complex C-star algebra represented on a complete "
                            + "complex inner-product space H. The family is a countable sequence "
                            + "of star projections in A, pairwise orthogonal, whose represented "
                            + "strong operator sum is the identity in pointwise form.")),
                    Paragraph(Text(
                        "The state is a positive linear functional normalized at the identity. "
                            + "Sequential normality is stated publicly as continuity along every "
                            + "monotone sequence with a strong pointwise limit.")),
                    Paragraph(Text(
                        "The theorem concludes both source clauses: the real state weights have "
                            + "sum one, and every vector has the pure-state Parseval sum of "
                            + "squared "
                            + "projection norms. A finite family is represented by zero extension "
                            + "of its sequence, while the displayed theorem handles the countable "
                            + "case directly.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies positivity of star projections, monotone operator "
                            + "partial sums, HasSum transport through continuous linear maps, and "
                            + "the inner-product norm identity. Repository and pinned-library "
                            + "searches found no theorem packaging the normal-state and Parseval "
                            + "clauses together."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula AdditivityFormula()
    {
        Formula scalar = Seq(Mathbb, Grp(F.Id("C")));
        Formula algebra = F.Id("A");
        Formula space = F.Id("H");
        Formula family = F.Id("P");
        Formula representation = F.Id("pi");
        Formula state = F.Id("omega");
        Formula vector = F.Id("psi");
        Formula index = F.Id("i");
        Formula index2 = F.Id("j");
        Formula zero = D(0);
        Formula one = D(1);
        Formula operatorType = Call("ContinuousLinearEnd", scalar, space);
        Formula representedProjection = Seq(representation, Open, Indexed(family, index), Close);
        Formula representedComponent = Seq(representedProjection, Open, vector, Close);
        Formula stateApplication = Seq(state, Open, Indexed(family, index), Close);
        Formula stateWeight = stateApplication;
        Formula componentNormSquared =
            Seq(new Formula.Norm(representedComponent), Caret, Grp(D(2)));
        Formula vectorNormSquared = Seq(new Formula.Norm(vector), Caret, Grp(D(2)));
        Formula sumState = Seq(Sum, Underscore, Grp(index), Sp, stateWeight, Eq, one);
        Formula sumPure = Seq(Sum, Underscore, Grp(index), Sp, componentNormSquared,
            Eq, vectorNormSquared);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(algebra, Seq(Operatorname, Grp(F.Id("Type")))), Comma, Sp,
            Typed(space, Seq(Operatorname, Grp(F.Id("Type")))), Comma, RowBreak, Grp(),
            OpenBracket, Call("CStarAlgebra", algebra), CloseBracket, Comma, Sp,
            OpenBracket, Call("PartialOrder", algebra), CloseBracket, Comma, Sp,
            OpenBracket, Call("StarOrderedRing", algebra), CloseBracket, Comma,
            RowBreak, Grp(),
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", scalar, space), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace", space), CloseBracket, Comma, RowBreak, Grp(),
            Typed(family, Seq(F.Id("Nat"), To, Sp, algebra)), Comma, RowBreak, Grp(),
            Typed(representation, Call("StarAlgHom", scalar, algebra, operatorType)), Comma, Sp,
            Typed(state, Call("PositiveLinearMap", scalar, algebra, scalar)), Comma,
            RowBreak, Grp(),
            OpenBracket, Forall, Sp, index, Comma, Sp,
            Call("IsStarProjection", Indexed(family, index)),
            CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Forall, Sp, index, Comma, Sp, index2, Comma, Sp,
            index, Neq, Sp, index2, Rightarrow, Sp,
            Indexed(family, index), Sp, Times, Sp, Indexed(family, index2), Eq, zero, CloseBracket,
            Comma, RowBreak, Grp(),
            OpenBracket, Forall, Sp, vector, Comma, Sp,
            Sum, Underscore, Grp(index), Sp, representedComponent, Eq, vector,
            CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, state, Open, one, Close, Eq, one, CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("SequentiallyNormal", representation, state), CloseBracket,
            Rightarrow, Sp,
            OpenBracket, sumState, Sp, Land, Sp, Forall, Sp, vector, Comma, Sp,
            sumPure, CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
