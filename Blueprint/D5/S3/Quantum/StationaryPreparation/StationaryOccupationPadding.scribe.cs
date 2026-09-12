using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class StationaryOccupationPaddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite padding isometries and the physical stationary occupation gate.",
        H("Stationary Occupation Padding"),
        Blocks(
            Paragraph(Text("For a finite tail alphabet I and natural capacities c, PaddingMemory(H,c) consists of a sink and pairs of a nonzero bounded tail with a head index in Fin(H+1). Each legal emission has the square root of its probability as its amplitude. The matrix maps each memory basis vector into the joint letter and memory space. Here coefficient(U,v,p)=(U v)(p) denotes the p coordinate of U(v).")),
            Theorem("padding-probability", "padding_probability_sum", "Padding transition probabilities sum to one", PaddingProbabilityFormula,
                "The sink, head predecessor and positive tail predecessors partition the legal emissions, including the one-tail boundary."),
            Theorem("padding-matrix", "padding_matrix_gram", "The padding matrix has orthonormal columns", PaddingMatrixFormula,
                "Distinct predecessor states have disjoint legal emissions in the (letter, memory) output space, and the probability identity gives unit column norm."),
            Theorem("padding-unitary", "padding_unitary_exists", "The padding matrix is realized by one unitary", PaddingUnitaryFormula,
                "The finite isometry extends to a unitary while preserving every displayed matrix coefficient."),
            Theorem("physical-gram", "physical_matrix_gram", "The physical matrix is an isometry",
                AlphabetContext(All("a", Multi, Eq(Mul(Call("conjTranspose", Call("physicalMatrix", Id("a"))), Call("physicalMatrix", Id("a"))), Call("identity", Call("Fin", Call("proposedDimension", Id("a"))))))),
                "Finite-index relabeling transports the padding Gram identity to physical memory coordinates."),
            Theorem("physical-final-norm", "physical_final_norm", "The physical sink vector is normalized",
                AlphabetContext(All("a", Multi, Eq(Call("norm", Call("physicalFinal", Id("a"))), D(1)))),
                "The final vector is the basis vector at the transported sink state."),
            Theorem("physical-coefficients", "physical_gate_coefficients", "Physical gate coefficients equal matrix entries",
                PhysicalCoefficientFormula,
                "The relabeled unitary exposes the exact weighted transition coefficient used by the residual circuit."))));

    private const string Prefix = "D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding.";
    private static Formula A => Id("A");
    private static Formula I => Id("I");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Multi => Call("Multiset", A);
    private static Formula PaddingProbabilityFormula => IndexDecidableContext(
        All("H", N, All("c", Function(I, N), All("s", Call("PaddingMemory", Id("H"), Id("c")),
            Eq(SumAt("i", Call("Option", I), Call("paddingProbability", Id("H"), Id("c"), Id("s"), Id("i"))), D(1))))));
    private static Formula PaddingMatrixFormula => IndexDecidableContext(
        All("H", N, All("c", Function(I, N), Eq(Mul(Call("conjTranspose", Call("paddingMatrix", Id("H"), Id("c"))),
            Call("paddingMatrix", Id("H"), Id("c"))), Call("identity", Call("PaddingMemory", Id("H"), Id("c")))))));
    private static Formula PaddingUnitaryFormula => IndexDecidableContext(
        All("H", N, All("c", Function(I, N), Exists("U", Call("Unitary", Call("Prod", Call("Option", I), Call("PaddingMemory", Id("H"), Id("c")))),
            All("j", Call("PaddingMemory", Id("H"), Id("c")), All("i", Call("Option", I), All("k", Call("PaddingMemory", Id("H"), Id("c")),
                Eq(Call("coefficient", Id("U"), Call("basis", Pair(Call("none"), Id("j"))), Pair(Id("i"), Id("k"))),
                    Call("paddingMatrix", Id("H"), Id("c"), Pair(Id("i"), Id("k")), Id("j"))))))))));
    private static Formula PhysicalCoefficientFormula => AlphabetContext(
        All("a", Multi, CoefficientsForA()));
    private static Formula CoefficientsForA()
    {
        var d = Call("Fin", Call("proposedDimension", Id("a")));
        var input = Call("basis", Pair(Call("maximalHead", Id("a")), Id("j")));
        var equation = Eq(Call("coefficient", Call("physicalGate", Id("a")), input,
            Pair(Id("i"), Id("k"))),
            Call("physicalMatrix", Id("a"), Pair(Id("i"), Id("k")), Id("j")));
        return All("j", d, All("i", A, All("k", d, equation)));
    }
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Pair(Formula left, Formula right) => Call("pair", left, right);
    private static Formula Function(Formula domain, Formula codomain) => Call("Function", domain, codomain);
    private static Formula SumAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] values) => values.Reverse().Aggregate((right, left) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula IndexDecidableContext(Formula body) => All("I", Id("Type"), Imp(And(Call("Fintype", I), Call("DecidableEq", I)), body));
    private static Formula AlphabetContext(Formula body) => All("A", Id("Type"), Imp(And(Call("Fintype", A), Call("DecidableEq", A), Call("Nonempty", A)), body));
    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string text) => Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
