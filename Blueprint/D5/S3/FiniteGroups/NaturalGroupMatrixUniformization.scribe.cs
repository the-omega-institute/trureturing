using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class NaturalGroupMatrixUniformizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/NaturalGroupMatrixUniformization.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => And(Implies(a, b), Implies(b, a));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Id(string name) => F.Id(name);
    private static Formula.BoundVariable[] GroupData => [
        B("H", Id("Type")), B("groupH", Call("Group", Id("H"))),
        B("finiteH", Call("Fintype", Id("H"))), B("n", Id("Nat"))];
    private static Formula GroupMat => Call("GroupMat", Id("H"), Id("n"), Id("n"));
    private static Formula Tau(string name) => Call("tau", Id(name));
    private static Formula UniformPower(string name) => Call("UniformMatrix", Call("matrixPower", Id(name), Id("k")));
    private static Formula TauClaim => All(Iff(Le(Tau("A"), Call("finiteWithTop", Id("k"))),
        And(Call("NatPositive", Id("k")), UniformPower("A"))),
        [.. GroupData, B("A", GroupMat), B("k", Id("Nat"))]);
    private static Formula OneClaim => All(Iff(Equal(Tau("A"), Call("finiteWithTop", D(1))),
        Call("UniformMatrix", Id("A"))), [.. GroupData, B("A", GroupMat)]);
    private static Formula PowerClaim => All(And(Call("NatPositive", Id("k")),
        Equal(Call("matrixPower", Id("A"), Id("k")), Call("matrixPower", Id("B"), Id("k")))),
        [.. GroupData, B("A", GroupMat), B("B", GroupMat),
         B("sameAugmentation", Equal(Call("matrixAugmentation", Id("A")), Call("matrixAugmentation", Id("B")))),
         B("k", Id("Nat")), B("threshold", Le(Call("max", Tau("A"), Tau("B")), Call("finiteWithTop", Id("k"))))]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least positive uniform exponent controls literal equality of natural group-matrix powers.",
        H("Positive natural uniformization time"), Blocks(
            Describe.Lean(DescribeId.Create("positive-tau-exact-threshold"),
                DeclarationHandle.Create(Prefix + "tau_le_iff_uniform_power"), H("Every admissible exponent"),
                StatementSource.FromAuthor(Disp(TauClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("GroupMat(H,n,n) is the matrix semiring over the natural group algebra. UniformMatrix means every actual group coefficient in each entry equals its coefficient at the identity, including zero coefficients. The value tau lies in the natural numbers with a top element: it is the least positive uniform exponent when one exists and infinity otherwise. Ordered convolution preserves uniformity under right multiplication, without assuming the finite group H is commutative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tau-one-uniform-boundaries"),
                DeclarationHandle.Create(Prefix + "tau_eq_one_iff_uniform"), H("The positive convention includes zero"),
                StatementSource.FromAuthor(Disp(OneClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence includes the zero matrix, whose least positive exponent is one even though its zeroth power behaves differently. If H is trivial, every entry is uniform and every matrix has tau one. It also includes n=0; no positivity of the matrix order is needed for the natural threshold theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("natural-powers-at-max-tau"),
                DeclarationHandle.Create(Prefix + "equal_power_of_tau_le"), H("Equal augmentation gives equal natural powers"),
                StatementSource.FromAuthor(Disp(PowerClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Augmentation sums the actual natural coefficients entry by entry and is a ring homomorphism. At every k at least both tau values, both powers are uniform. A uniform natural entry is determined by its augmentation because its coefficient sum is |H| times any coefficient and |H| is positive. Thus A^k=B^k in the original natural group-matrix semiring. Positivity of k is a conclusion; k=1 is retained."))), DescribeRole.Theorem))));
}
