using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class ToralFixedPointCokernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Dynamics/ToralFixedPointCokernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual periodic points of the continuous integer action on R^2/Z^2 realize the existing return cokernels.",
        H("Actual torus periodic points and return cokernels"),
        Blocks(
            Paragraph(Text("The torus is the real plane modulo the image of the coordinatewise integer inclusion, "
                + "with its quotient topology. Its periodic subgroup is the kernel of the actual induced "
                + "map A^n-I. A point in this subgroup is fixed by the nth iterate, which allows a smaller least period.")),
            Describe.Lean(DescribeId.Create("continuous-actual-torus-action"),
                DeclarationHandle.Create(Prefix + "torusAction_continuous"),
                H("The original integer matrix induces a continuous quotient action"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Colon, Sp, Call("Mat2", Call("Integer")), Comma, Sp,
                    Call("Continuous", Call("torusAction", F.Id("A")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real linear action preserves the embedded integer lattice. "
                    + "Submodule.mapQ constructs the quotient map. Its composition with the quotient projection "
                    + "is continuous, so the quotient-map criterion proves continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-periodic-subgroup"),
                DeclarationHandle.Create(Prefix + "mem_periodicGroup_iff"),
                H("Membership means equality after the actual time iterate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A,n,z"), Comma, Sp,
                    Call("Member", F.Id("z"), Call("PeriodicGroup", F.Id("A"), F.Id("n"))),
                    Sp, Call("iff"), Sp,
                    Call("iterate", Call("torusAction", F.Id("A")), F.Id("n"), F.Id("z")),
                    Sp, Eq, Sp, F.Id("z")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A is an integer two-by-two matrix, n is a natural number and z is an actual "
                    + "torus point. Matrix multiplication agrees with quotient-map composition and the identity "
                    + "matrix acts identically. Induction identifies matrix powers with iterates, then subtraction "
                    + "identifies the return kernel with precisely the nth fixed-point set."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integer-lift-exact-kernel"),
                DeclarationHandle.Create(Prefix + "integerToTorusKernel_ker"),
                H("The constructed inverse-matrix lift has exactly the original return image as kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("M"), Colon, Sp, Call("Mat2", Call("Integer")), Comma, Sp,
                    Call("NotEqual", Call("det", F.Id("M")), D(0)), Sp, Rightarrow, Sp,
                    Call("ker", Call("integerToTorusKernel", F.Id("M"))), Sp, Eq, Sp,
                    Call("range", Call("toLin", F.Id("M")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map sends an integer vector z to the class of M^{-1}z in the real torus. "
                    + "The inverse is the explicit adjugate divided by the nonzero real determinant. "
                    + "This class vanishes exactly when M^{-1}z is an integer vector, equivalently z is in M Z^2. "
                    + "A torus point in the kernel has Mx integral, which proves surjectivity of the same map. "
                    + "returnModuleEquivPeriodicGroup applies the first isomorphism theorem to these actual maps."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-actual-periodic-cardinalities"),
                DeclarationHandle.Create(Prefix + "equal_actual_periodic_cardinalities"),
                H("The original infinite family has equal all-time counts of actual torus points"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k,n"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Call("Positive", F.Id("k")), Sp, Land, Sp, Call("Positive", F.Id("n")),
                    Sp, Rightarrow, Sp, Card("C"), Sp, Eq, Sp, Card("D"), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, Card("C")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C_k,D_k are the original matrices of ToralReturnModuleSpectrum. "
                    + "Their return determinants are nonzero at all positive parameters and times, as already proved "
                    + "from actual matrix powers. The constructed equivalences transport the existing quotient "
                    + "cardinality equality and positivity to the actual periodic subgroups. No periodic count "
                    + "or missing object-identification equality is supplied as a hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-fixed-group-separation"),
                DeclarationHandle.Create(Prefix + "actual_fixed_groups_not_isomorphic"),
                H("The one-step fixed groups still differ as additive groups"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Call("Positive", F.Id("k")), Sp, Rightarrow, Sp,
                    Call("Not", Call("Nonempty", Call("AddEquiv",
                        Call("PeriodicGroup", F.Id("C_k"), D(1)),
                        Call("PeriodicGroup", F.Id("D_k"), D(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A putative additive isomorphism of actual fixed groups would transport "
                    + "through the constructed equivalences to an isomorphism of the original return modules, "
                    + "contradicting their proven exponent separation. This concerns actual torus point groups. "
                    + "It is not a mapping-torus homology computation or a three-manifold homeomorphism theorem. "
                    + "The underlying correspondence is classical, in the Bowen-Franks setting."))),
                DescribeRole.Theorem))));

    private static Formula Card(string matrix) =>
        Call("Nat.card", Call("PeriodicGroup", F.Id(matrix + "_k"), F.Id("n")));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
