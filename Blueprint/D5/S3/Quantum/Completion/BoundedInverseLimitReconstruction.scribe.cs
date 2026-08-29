using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class BoundedInverseLimitReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded compatible projection families reconstruct the cumulative Hilbert completion.",
        H("Bounded Inverse-Limit Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-inverse-limit-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction."
                        + "bounded_inverse_limit_reconstruction"),
                H("Bounded compatible families reconstruct the cumulative completion"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a monotone sequence of closed subspaces of a complete Hilbert "
                            + "space. Its bounded inverse limit is constructed as the subspace of "
                            + "bounded families x_n with x_n in S_n and with every earlier "
                            + "coordinate equal to the orthogonal projection of every later one.")),
                    Paragraph(Text(
                        "The canonical map J sends x in the closure of the union of the stages to "
                            + "the family of its orthogonal projections. Increasing projection "
                            + "convergence proves that J preserves the norm. Conversely, projection "
                            + "compatibility gives a Pythagorean identity for coordinate differences; "
                            + "bounded squared norms therefore make every compatible family Cauchy.")),
                    Paragraph(Text(
                        "The family limit lies in the cumulative closure and has exactly the given "
                            + "stage projections, proving bijectivity. The quotient conclusion is "
                            + "obtained by composing J with Mathlib's canonical isometry from the "
                            + "quotient by the residual orthogonal complement to the cumulative "
                            + "space."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ReconstructionFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula stages = F.Id("S");
        Formula monotonicity = F.Id("hS");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula cumulative = Call("cumulativeSpace", stages);
        Formula residual = Call("residualSpace", stages);
        Formula limit = Call("boundedInverseLimit", stages);
        Formula canonical = Call("canonicalReconstructionEquiv", stages, monotonicity);
        Formula quotientMap = Call("quotientReconstructionEquiv", stages, monotonicity);
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula boundedFunction = Call("BoundedContinuousFunction", naturals, space);
        Formula canonicalFunction = Seq(
            Open, canonical, Colon, Sp, cumulative, Sp, To, Sp, limit, Close);
        Formula quotientFunction = Seq(
            Open, quotientMap, Colon, Sp,
            Call("Quotient", space, residual), Sp, To, Sp, limit, Close);

        Formula isometryJ = Call("Isometry", canonicalFunction);
        Formula bijectiveJ = Call("Bijective", canonicalFunction);
        Formula coordinateFormula = Seq(
            Forall, Sp, x, Colon, Sp, cumulative, Comma, Sp,
            Forall, Sp, n, Colon, Sp, naturals, Comma, Esc,
            Apply(
                Seq(
                    Open,
                    Seq(Open, Apply(canonical, x), Colon, Sp, limit, Close),
                    Colon, Sp, boundedFunction,
                    Close),
                n),
            Sp, Eq, Sp,
            Call("starProjection", Apply(stages, n), Seq(Open, x, Colon, Sp, space, Close)));
        Formula isometryQ = Call("Isometry", quotientFunction);
        Formula bijectiveQ = Call("Bijective", quotientFunction);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("RCLike", scalar), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("InnerProductSpace", scalar, space), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace", space), CloseBracket, Comma, RowBreak, Grp(),
            stages, Colon, Sp, naturals, Sp, To, Sp,
            Call("Submodule", scalar, space), Comma, RowBreak, Grp(),
            OpenBracket,
            Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            Call("HasOrthogonalProjection", Apply(stages, n)),
            CloseBracket, Comma, RowBreak, Grp(),
            monotonicity, Colon, Sp, Call("Monotone", stages), Comma, RowBreak, Grp(),
            isometryJ, Sp, Land, Sp,
            bijectiveJ, Sp, Land, Sp,
            Open, coordinateFormula, Close, Sp, Land, RowBreak, Grp(),
            isometryQ, Sp, Land, Sp,
            bijectiveQ, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
