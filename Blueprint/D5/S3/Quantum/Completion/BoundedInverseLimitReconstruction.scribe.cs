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

    private static Formula ReconstructionFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("H");
        Formula stages = F.Id("S");
        Formula cumulative = F.Id("Sinfinity");
        Formula residual = F.Id("Rinfinity");
        Formula limit = Call("BoundedInverseLimit", stages);
        Formula canonical = F.Id("J");
        Formula quotientMap = F.Id("Q");
        Formula x = F.Id("x");
        Formula n = F.Id("n");

        Formula isometryJ = Call("Isometry", canonical);
        Formula bijectiveJ = Call("Bijective", canonical);
        Formula coordinateFormula = Seq(
            Forall, Sp, x, Sp, InMacro, Sp, cumulative, Comma, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Call("coord", Call("apply", canonical, x), n), Sp, Eq, Sp,
            Call("orthogonalProjection", Call("apply", stages, n), x));
        Formula isometryQ = Call("Isometry", quotientMap);
        Formula bijectiveQ = Call("Bijective", quotientMap);

        return Disp(Seq(
            Forall, Sp, scalar, Colon, Sp, Call("RCLikeField"), Comma, Esc,
            Forall, Sp, space, Colon, Sp, Call("CompleteHilbertSpace", scalar), Comma, Esc,
            Forall, Sp, stages, Colon, Sp,
            Call("Sequence", Call("Submodule", scalar, space)), Comma, Esc,
            Call("Monotone", stages), Sp, Land, Sp,
            Call("HasOrthogonalProjection", stages), Comma, Esc,
            cumulative, Sp, Eq, Sp, Call("ClosureUnion", stages), Comma, Esc,
            residual, Sp, Eq, Sp, Call("OrthogonalComplement", cumulative), Comma, Esc,
            canonical, Colon, Sp, cumulative, Sp, To, Sp, limit, Comma, Esc,
            quotientMap, Colon, Sp, Call("Quotient", space, residual), Sp, To, Sp, limit,
            Comma, Esc,
            isometryJ, Sp, Land, Sp,
            bijectiveJ, Sp, Land, Sp,
            Open, coordinateFormula, Close, Sp, Land, Sp,
            isometryQ, Sp, Land, Sp,
            bijectiveQ, Dot));
    }
}
