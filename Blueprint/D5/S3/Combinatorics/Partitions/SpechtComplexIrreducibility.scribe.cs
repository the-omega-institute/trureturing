using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtComplexIrreducibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Specht ComplexIrreducibility",
        H("Specht ComplexIrreducibility"),
        Blocks(
            Paragraph(Text("The intertwining condition is the kernel of the linear map recording commutation defects. Finite free scalar extension identifies the ambient linear-map spaces, and flatness preserves the kernel. The intertwiner dimension survives complexification. Rational scalarity makes the complex endomorphism space one dimensional. The finite-group character norm criterion gives simplicity of the complex scalar extension of the same literal partition-indexed Specht module. The three-row Cauchy and mixed pairings supply the subsequent comparison with the Frobenius coefficient.")),
            Paragraph(Text("ModuleOver means an additive commutative group with the indicated module structure in the intertwiner statements. In the semiring action identity it means an additive commutative monoid with that module structure. FiniteMonoid includes no commutativity assumption. The linear equivalence by flat kernel base change maps the scalar extension of the original intertwiner space to the intertwiners between the two extended actions.")),
            Describe.Lean(DescribeId.Create("isbasechange-basechangehom"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.isBaseChange_baseChangeHom"),
                H("isBaseChange baseChangeHom"), StatementSource.FromAuthor(Disp(A("R", C("Type"), A("A", C("Type"), A("M", C("Type"), A("N", C("Type"), P(C("CommSemiring", I("R")), P(C("CommSemiring", I("A")), P(C("Algebra", I("R"), I("A")), P(C("AddCommMonoid", I("M")), P(C("Module", I("R"), I("M")), P(C("ModuleFree", I("R"), I("M")), P(C("ModuleFinite", I("R"), I("M")), P(C("AddCommMonoid", I("N")), P(C("Module", I("R"), I("N")), C("IsBaseChange", I("A"), C("linearMapBaseChangeHom", I("R"), I("A"), I("M"), I("N")))))))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("basechange-apply"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.baseChange_apply"),
                H("baseChange apply"), StatementSource.FromAuthor(Disp(A("R", C("CommSemiring"), A("A", C("SemiringAlgebraOver", I("R")), A("G", C("Monoid"), A("V", C("ModuleOver", I("R")), A("rho", C("Representation", I("R"), I("G"), I("V")), A("g", I("G"), Q(C("action", C("baseChange", I("A"), I("rho")), I("g")), C("linearMapBaseChange", I("A"), C("action", I("rho"), I("g")))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("intertwiningmapbasechangeequiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.intertwiningMapBaseChangeEquiv"),
                H("intertwiningMapBaseChangeEquiv"), StatementSource.FromAuthor(Disp(A("K", C("CommRing"), A("L", C("CommRingAlgebraOver", I("K")), A("G", C("FiniteMonoid"), A("V", C("FiniteFreeModuleOver", I("K")), A("W", C("ModuleOver", I("K")), P(C("ModuleFlat", I("K"), I("L")), A("rho", C("Representation", I("K"), I("G"), I("V")), A("sigma", C("Representation", I("K"), I("G"), I("W")), Q(C("intertwiningMapBaseChangeEquiv", I("rho"), I("sigma")), C("linearEquivalenceByFlatKernelBaseChange", I("L"), C("Intertwiner", I("rho"), I("sigma")), C("Intertwiner", C("baseChange", I("L"), I("rho")), C("baseChange", I("L"), I("sigma"))))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finrank-intertwiningmap-basechange"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.finrank_intertwiningMap_baseChange"),
                H("finrank intertwiningMap baseChange"), StatementSource.FromAuthor(Disp(A("K", C("Field"), A("L", C("NontrivialCommRingAlgebraOver", I("K")), A("G", C("FiniteMonoid"), A("V", C("FiniteDimensionalModuleOver", I("K")), A("W", C("ModuleOver", I("K")), A("rho", C("Representation", I("K"), I("G"), I("V")), A("sigma", C("Representation", I("K"), I("G"), I("W")), Q(C("finrank", I("L"), C("Intertwiner", C("baseChange", I("L"), I("rho")), C("baseChange", I("L"), I("sigma")))), C("finrank", I("K"), C("Intertwiner", I("rho"), I("sigma"))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spechtmodulec-def"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.spechtModuleℂ_def"),
                H("spechtModuleℂ def"), StatementSource.FromAuthor(Disp(Part(Q(C("spechtModuleComplex", I("mu")), C("FDRepOf", C("baseChange", C("Complex"), C("rationalSpechtAction", I("mu")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("instsimplespechtmodulec"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtComplexIrreducibility.instSimpleSpechtModuleℂ"),
                H("instSimpleSpechtModuleℂ"), StatementSource.FromAuthor(Disp(Part(C("Simple", C("spechtModuleComplex", I("mu")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(I(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Q(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula P(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Part(Formula body) => A("n", C("Nat"), A("mu", C("Partition", I("n")), body));
}
