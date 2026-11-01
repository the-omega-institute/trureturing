using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class DetectedOrderTwoHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/DetectedOrderTwoHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mod-two functional detects a nonzero order-two class in integral ModuleCat homology.",
        H("Detecting an integral homology class of order two"),
        Blocks(
            Paragraph(Text(
                "Source artifact against project 47c4bf60b02ba7c24acba82e8451ef78dca9ac60 and Mathlib "
                + "56a005855ea17e0b0958f73ec801ae140b0a1679. No elaboration, kernel check, Scribe build, "
                + "registration, or publication has run at this source-only stage.")),
            Node("cycle-class-map", "cycleClassMap", "The class map into actual categorical homology",
                "For every short complex S of integer modules, cycleClassMap S is the integer-linear map "
                + "from the concrete kernel of S.g to S.homology. It first takes the quotient by the range "
                + "of S.moduleCatToCycles and then applies the inverse of Mathlib's moduleCatHomologyIso. "
                + "Thus its codomain is the existing ShortComplex homology object, not an unrelated quotient.",
                DescribeRole.Definition),
            Node("class-zero-iff-boundary", "cycleClassMap_eq_zero_iff", "A class vanishes exactly when it bounds",
                "For every S : ShortComplex (ModuleCat Z) and z in LinearMap.ker S.g.hom, "
                + "cycleClassMap S z = 0 if and only if there exists c in S.X1 with S.f c = z. "
                + "The proof uses the exact ModuleCat homology isomorphism and quotient-zero criterion.",
                DescribeRole.Theorem),
            Node("detected-order-two", "detected_order_two", "A detected cycle whose double bounds",
                "For every short complex S of integer modules, every z in the kernel of S.g, every c in S.X1 "
                + "with S.f c = 2 times z, and every integer-linear map phi from S.X2 to ZMod 2 which is "
                + "zero on S.f b for all b in S.X1 and is nonzero on z, the actual class cycleClassMap S z "
                + "is nonzero and its double is zero. These hypotheses impose no finiteness or exactness "
                + "assumptions on the other classes. The eleven-vertex independence-complex seed consumes "
                + "this construction; no singular-homology comparison is part of this theorem.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
