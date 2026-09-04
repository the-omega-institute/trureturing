using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class LawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite catalog laws for labels, primitive kernels, irredundancy, and augmentation.",
        H("Information Escape Catalog Laws"),
        Blocks(
            Def("catalog-reindex", "reindex", "Catalog reindexing",
                Eq(Call("Index", Call("reindex", C, E)), J)),
            Def("catalog-with-theorem-at", "withTheoremAt", "Catalog theorem-family replacement",
                Eq(Call("Index", Call("withTheoremAt", C, U)), Call("Index", C))),
            Thm("escape-pairs-reindex", "escapePairs_reindex",
                "Every selected escape finset is invariant under reindexing",
                UnderIndexEquivalence(Eq(Call("escapePairs", Call("reindex", C, E),
                        Call("map", Call("toEmbedding", E), A)),
                    Call("escapePairs", C, A)))),
            Thm("escape-rate-reindex", "escapeRate_reindex",
                "Every selected escape rate is invariant under reindexing",
                UnderIndexEquivalence(Eq(Call("escapeRate", Call("reindex", C, E),
                        Call("map", Call("toEmbedding", E), A)),
                    Call("escapeRate", C, A)))),
            Thm("unique-capture-count-reindex", "uniqueCaptureCount_reindex",
                "Unique capture is invariant under reindexing",
                UnderIndexEquivalence(Eq(
                    Call("uniqueCaptureCount", Call("reindex", C, E), Call("apply", E, I)),
                    Call("uniqueCaptureCount", C, I)))),
            Thm("theorem-gain-rate-reindex", "theoremGainRate_reindex",
                "Exact theorem gain is invariant under reindexing",
                UnderIndexEquivalence(Eq(
                    Call("theoremGainRate", Call("reindex", C, E), Call("apply", E, I)),
                    Call("theoremGainRate", C, I)))),
            Thm("unique-capture-count-congr-kernel", "uniqueCaptureCount_congr_kernel",
                "Pointwise kernel equality preserves every unique capture count",
                Implies(KernelEquivalent(C, U),
                    Eq(Call("uniqueCaptureCount", Call("withTheoremAt", C, U), I),
                        Call("uniqueCaptureCount", C, I)))),
            Thm("unique-capture-pairs-congr-kernel", "uniqueCapturePairs_congr_kernel",
                "Pointwise kernel equality preserves every unique capture finset",
                Implies(KernelEquivalent(C, U),
                    Eq(Call("uniqueCapturePairs", Call("withTheoremAt", C, U), I),
                        Call("uniqueCapturePairs", C, I)))),
            Thm("escape-pairs-congr-kernel", "escapePairs_congr_kernel",
                "Pointwise kernel equality preserves full-catalog escape pairs",
                Implies(KernelEquivalent(C, U),
                    Eq(FullEscapePairs(Call("withTheoremAt", C, U)), FullEscapePairs(C)))),
            Thm("escape-count-congr-kernel", "escapeCount_congr_kernel",
                "Pointwise kernel equality preserves the full-catalog escape count",
                Implies(KernelEquivalent(C, U),
                    Eq(Call("card", FullEscapePairs(Call("withTheoremAt", C, U))),
                        Call("card", FullEscapePairs(C))))),
            Thm("escape-rate-congr-kernel", "escapeRate_congr_kernel",
                "Pointwise kernel equality preserves the full-catalog escape rate",
                Implies(KernelEquivalent(C, U),
                    Eq(FullEscapeRate(Call("withTheoremAt", C, U)), FullEscapeRate(C)))),
            Thm("unique-capture-count-congr-primitive-realization",
                "uniqueCaptureCount_congr_primitiveRealization",
                "Kernel-equivalent primitive realizations have identical counts",
                Implies(AgreementEquivalent(R, S),
                    Eq(Call("uniqueCaptureCount",
                            Call("withTheoremAt", C, ReplacementFamily(R)), I),
                        Call("uniqueCaptureCount",
                            Call("withTheoremAt", C, ReplacementFamily(S)), I)))),
            Def("catalog-irredundant", "CatalogIrredundant", "Catalog irredundancy",
                Eq(Call("CatalogIrredundant", C),
                    Seq(Forall, Sp, I, Comma, Sp, Call("LowersEscape", C, I)))),
            Thm("catalog-irredundant-iff-forall-pos", "catalogIrredundant_iff_forall_pos",
                "Irredundancy is positivity of all unique captures",
                Seq(Call("CatalogIrredundant", C), Sp, Leftrightarrow, Sp,
                    Forall, Sp, I, Comma, Sp,
                    Lt(D(0), Call("uniqueCaptureCount", C, I)))),
            Def("augmented-statement", "AugmentedStatement", "Augmented theorem statement",
                Eq(Call("AugmentedStatement", C, I),
                    Call("And", Call("Statement", Call("theoremAt", C, I)),
                        Call("LowersEscape", C, I)))),
            Thm("augmented-proof", "augmentedProof", "Augmented theorem proof constructor",
                Implies(Call("LowersEscape", C, I), Call("AugmentedStatement", C, I))),
            Thm("catalog-all-augmented", "catalog_all_augmented",
                "Every theorem in an irredundant catalog is augmented",
                Implies(Call("CatalogIrredundant", C),
                    Seq(Forall, Sp, I, Comma, Sp, Call("AugmentedStatement", C, I)))))));

    private static readonly Formula A = F.Id("A");
    private static readonly Formula C = F.Id("C");
    private static readonly Formula E = F.Id("e");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula J = F.Id("J");
    private static readonly Formula K = F.Id("k");
    private static readonly Formula L = F.Id("x");
    private static readonly Formula N = F.Id("j");
    private static readonly Formula R = F.Id("R");
    private static readonly Formula S = F.Id("S");
    private static readonly Formula U = F.Id("U");
    private static readonly Formula Y = F.Id("y");

    private static DocumentBlock Def(string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), Handle(declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This definition is computed from the finite catalog and its canonical primitive kernels."))),
            DescribeRole.Definition);

    private static DocumentBlock Thm(string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), Handle(declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The proof uses the frozen finite-kernel and exact-count APIs."))),
            DescribeRole.Theorem);

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(
            "D5/S3/ConceptDynamics/InformationEscape/Laws." + declaration);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Eq(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula KernelEquivalent(Formula catalog, Formula units) =>
        Seq(Open, Forall, Sp, N, Comma, Sp, L, Comma, Sp, Y, Comma, Sp,
            Call("relation", Call("toKernel", Call("primitives", Call("theoremAt", catalog, N))), L, Y),
            Sp, Leftrightarrow, Sp,
            Call("relation", Call("toKernel", Call("primitives", Call("apply", units, N))), L, Y), Close);

    private static Formula AgreementEquivalent(Formula first, Formula second) =>
        Seq(Open, Forall, Sp, L, Comma, Sp, Y, Comma, Sp,
            Call("agrees", Call("toPrimitiveBundle", first), L, Y),
            Sp, Leftrightarrow, Sp,
            Call("agrees", Call("toPrimitiveBundle", second), L, Y), Close);

    private static Formula ReplacementFamily(Formula realization) =>
        Seq(Open, N, Sp, Mapsto, Sp,
            Call("ite", Eq(N, K),
                Call("TheoremUnit", Call("toPrimitiveBundle", realization),
                    Call("Statement", Call("theoremAt", C, N)),
                    Call("proof", Call("theoremAt", C, N))),
                Call("theoremAt", C, N)), Close);

    private static Formula FullEscapePairs(Formula catalog) =>
        Call("escapePairs", catalog, Call("fullIndexSet", catalog));

    private static Formula FullEscapeRate(Formula catalog) =>
        Call("escapeRate", catalog, Call("fullIndexSet", catalog));

    private static Formula UnderIndexEquivalence(Formula conclusion) =>
        Seq(Forall, Sp, E, Colon, Sp, Call("Index", C), Sp, Equiv, Sp, J,
            Comma, Sp, conclusion);
}
