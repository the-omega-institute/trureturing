using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.RandomCircuits;

internal sealed class BalancedOrbitMarginalEntropyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/zhangxiang2017averageentropyorbit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two marginals of a balanced bipartite density state have equal Haar-averaged von Neumann entropies over its global unitary orbit.",
        H("Equal average marginal entropies on a balanced unitary orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("balanced-orbit-marginal-entropy-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The balanced marginal entropy identity"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n and every positive semidefinite trace-one state on the pair of n-dimensional factors, conjugate the state by a global unitary u. The right partial trace sums over the second coordinate, and the left partial trace sums over the first. The proposition equates the real Bochner integrals of the von Neumann entropies of these marginals against normalized Haar measure on the global unitary group. The top positive compact set is the entire compact group and fixes the Haar normalization. This is the balanced identity asked for in QINP-D-16-00527-revision.tex, lines 916–920, item (ii). The quantifiers range over all such states, including mixed states of arbitrary rank."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("balanced-orbit-marginal-entropy-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Haar symmetry equates the two averages"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let F be the permutation unitary associated with Equiv.prodComm on Fin n × Fin n. It exchanges the two coordinates. For any complex matrix x on this product, conjugation by F exchanges the partial traces: the right partial trace of F x F† is the left partial trace of x. Indeed, its entry at i,j is the sum over k of the entries of x at (k,i),(k,j), exactly the left partial trace.")),
                    Paragraph(Text(
                        "Apply this matrix identity to u ρ u†. The adjoint of the product F u is u† F†, and associativity identifies (F u) ρ (F u)† with F (u ρ u†) F†. Passing through the matrix representation of density states and using equality of their underlying matrices gives equality of the right marginal at F u and the left marginal at u.")),
                    Paragraph(Text(
                        "For each n and ρ, first use left invariance of Haar measure to replace u by F u in the integral of the right marginal entropy. The marginal equality then gives equality of the two entropy integrands at every u, hence almost everywhere. Equality of their integrals proves the displayed identity, answering item (ii) in QINP-D-16-00527-revision.tex, lines 916–920."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        Formula n = X("n");
        return All(n, Naturals(), All(Rho, DensityType(n),
            Equal(MarginalEntropyIntegral(n, "marginalRight"),
                MarginalEntropyIntegral(n, "marginalLeft"))));
    }

    private static Formula MarginalEntropyIntegral(Formula n, string marginal)
    {
        Formula u = X("u");
        Formula matrix = Typed(At(Qualified("Subtype", "val"), u), MatrixType(n));
        Formula conjugate = At(Qualified("D5", "S3", "Quantum", "Dynamics",
            "EntropyProductionCoherenceDeletionIdentity", "unitaryConjugateState"),
            matrix, At(Qualified("Subtype", "property"), u), Rho);
        Formula entropy = At(Qualified("D5", "S3", "Quantum", "Divergence",
            "VonNeumannEntropyPinching", "vonNeumannEntropy"),
            At(Qualified("D5", "S3", "Quantum", "Information",
                "PartialTraceMutualInformation", marginal), conjugate));
        Formula measure = At(Qualified("MeasureTheory", "Measure", "haarMeasure"),
            Typed(Qualified("Top", "top"),
                At(Qualified("TopologicalSpace", "PositiveCompacts"), UnitaryType(n))));
        return At(Qualified("MeasureTheory", "integral"), measure,
            LambdaOf(u, UnitaryType(n), entropy));
    }

    private static Formula DensityType(Formula n) => At(Qualified("D5", "S3", "Quantum",
        "Divergence", "QuantumRelativeEntropyDefectComposition", "DensityState"), IndexType(n));

    private static Formula IndexType(Formula n) => Parenthesized(Seq(
        At(Qualified("Fin"), n), Sp, Times, Sp, At(Qualified("Fin"), n)));

    private static Formula MatrixType(Formula n) =>
        At(Qualified("Matrix"), IndexType(n), IndexType(n), Complex());

    private static Formula UnitaryType(Formula n) =>
        At(Qualified("CoeSort", "coe"),
            At(Qualified("Matrix", "unitaryGroup"), IndexType(n), Complex()));

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum",
        "RandomCircuits", "BalancedOrbitMarginalEntropy", name);

    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
}
