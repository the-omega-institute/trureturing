using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class RationalGroupAlgebraSplittingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/RationalGroupAlgebraSplitting.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => And(Implies(a, b), Implies(b, a));
    private static Formula Id(string name) => F.Id(name);
    private static Formula.BoundVariable[] GroupData => [
        B("H", Id("Type")), B("groupH", Call("Group", Id("H"))), B("finiteH", Call("Fintype", Id("H")))];
    private static Formula AlgebraH => Call("MonoidAlgebra", Id("Rat"), Id("H"));
    private static Formula TailClaim => All(Iff(Call("UniformRational", Id("x")),
        Equal(Call("second", Call("apply", Id("phi"), Id("x"))), D(0))),
        [.. GroupData, B("S", Id("Type")), B("ringS", Call("Ring", Id("S"))),
         B("algebraS", Call("Algebra", Id("Rat"), Id("S"))),
         B("phi", Call("AlgEquiv", Id("Rat"), AlgebraH, Call("Product", Id("Rat"), Id("S")))),
         B("augmentationFirst", All(Equal(Call("first", Call("apply", Id("phi"), Id("z"))),
             Call("augmentation", Id("z"))), B("z", AlgebraH))), B("x", AlgebraH)]);
    private static Formula ExistenceClaim => All(Call("Nonempty", Call("RationalDecomposition", Id("H"))),
        [.. GroupData, B("nontrivialH", Call("Nontrivial", Id("H")))]);
    private static Formula UniformClaim => All(Equal(Id("x"),
        Call("scalarMultiply", Call("augmentation", Id("x")), Call("average", Id("H")))),
        [.. GroupData, B("x", AlgebraH), B("uniform", Call("UniformRational", Id("x")))]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual uniform ideal separates augmentation before the nontrivial rational Wedderburn blocks are chosen.",
        H("Augmentation-first rational group algebra"), Blocks(
            Describe.Lean(DescribeId.Create("uniform-tail-kernel"),
                DeclarationHandle.Create(Prefix + "uniform_iff_tail_zero"), H("The exact kernel of the nontrivial tail"),
                StatementSource.FromAuthor(Disp(TailClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UniformRational means equality of every coefficient with the identity coefficient. Augmentation is their rational sum. The normalized element average(H), denoted e_H, has every coefficient 1/|H|. The theorem applies to any actual rational algebra equivalence phi whose first coordinate is literally augmentation; S may be noncommutative. A uniform element satisfies x*y=augmentation(y) times x. Conversely, vanishing tail makes every left group translation fix x and hence makes every coefficient equal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("augmentation-first-rational-decomposition"),
                DeclarationHandle.Create(Prefix + "nonempty_decomposition"), H("All nontrivial rational simple factors"),
                StatementSource.FromAuthor(Disp(ExistenceClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("RationalDecomposition(H) consists of a positive count m, a division algebra D_l over the rationals of finite rational dimension for each l in Fin(m), positive natural matrix orders r_l, and an actual rational algebra equivalence Q[H] with Q times the product of Mat(r_l,D_l). Its first coordinate equals augmentation on every element. No complex splitting or change of coefficient field occurs.")),
                    Paragraph(Text("Uniform elements form a two-sided ideal J. The map x to (augmentation(x),[x]) is bijective: its kernel is zero because a uniform augmentation-zero element is zero, and a preimage of (a,[x]) is x+(a-augmentation(x))*e_H. For nontrivial H the quotient Q[H]/J is nontrivial. Maschke supplies semisimplicity and the finite rational Wedderburn theorem supplies the division-ring factors of this quotient. The quotient's nontriviality makes the factor count positive; no empty maximum is assigned to a trivial group."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-normalized-rational-expression"),
                DeclarationHandle.Create(Prefix + "uniform_eq_augmentation_smul_average"), H("The exact normalized expression"),
                StatementSource.FromAuthor(Disp(UniformClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every uniform rational element is its actual augmentation times e_H. This includes zero and preserves the factor 1/|H| exactly."))), DescribeRole.Theorem))));
}
