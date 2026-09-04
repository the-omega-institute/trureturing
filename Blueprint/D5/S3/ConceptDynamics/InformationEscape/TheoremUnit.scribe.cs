using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class TheoremUnitDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/TheoremUnit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed primitive realizations compile theorem laws into finite executable catalogs.",
        H("Information-Escape Theorem Units"),
        Blocks(
            DefinitionNode("primitive-signature", "PrimitiveSignature", "Primitive signature",
                "A signature records typed readouts and separately indexed point anchors."),
            DefinitionNode("primitive-realization", "PrimitiveRealization", "Primitive realization",
                "A realization supplies every typed readout and every anchor point."),
            DefinitionNode("realization-to-bundle", "PrimitiveRealization.toPrimitiveBundle",
                "Realization bundle",
                "Readouts compile to CUT atoms while points compile to ANCHOR atoms."),
            TheoremNode("realization-bundle-agreement",
                "PrimitiveRealization.toPrimitiveBundle_agrees_iff",
                "Compiled agreement has the typed signature semantics", AgreementFormula(),
                "The sum-indexed bundle agrees exactly when all readouts match and all point-anchor tests match."),
            TheoremNode("admit-boolean-readout-reflection", "admit_readout_eq_true_iff",
                "Boolean ADMIT readout reflection", AdmitFormula(),
                "Deciding the admission predicate yields true exactly when the predicate holds."),
            DefinitionNode("theorem-unit", "TheoremUnit", "Theorem unit",
                "A theorem unit pairs a proved statement with its object-level primitive bundle."),
            DefinitionNode("primitive-law-arena", "PrimitiveLawArena", "Primitive-law arena",
                "A primitive-law arena extends a finite arena with a typed signature and laws over its realizations."),
            DefinitionNode("native-theorem-unit", "NativeTheoremUnit", "Native theorem unit",
                "A native unit proves the arena law directly for its realization."),
            DefinitionNode("legacy-primitive-realization", "LegacyPrimitiveRealization",
                "Legacy primitive realization",
                "A legacy realization proves equivalence between an existing statement and its primitive law."),
            DefinitionNode("native-unit-erasure", "NativeTheoremUnit.toTheoremUnit",
                "Native unit erasure",
                "Erasure retains the compiled bundle and the native primitive law."),
            DefinitionNode("legacy-unit-erasure", "LegacyPrimitiveRealization.toTheoremUnit",
                "Legacy unit erasure",
                "A proved legacy statement is packaged with its realization's compiled bundle."),
            DefinitionNode("theorem-catalog", "Catalog", "Theorem catalog",
                "A catalog is a finite decidable index of theorem units over one arena."),
            DefinitionNode("catalog-from-vector", "Catalog.ofVector", "Catalog from a vector",
                "A Fin-indexed vector is the canonical fixed-length catalog constructor."),
            DefinitionNode("catalog-full-index-set", "Catalog.fullIndexSet", "Full index set",
                "The full catalog selection is the universal finite set."),
            DefinitionNode("catalog-without-index", "Catalog.without", "Leave-one-out set",
                "The leave-one-out set erases one theorem from the full selection."),
            TheoremNode("catalog-without-membership", "Catalog.mem_without_iff",
                "Leave-one-out membership", WithoutMembershipFormula(),
                "A candidate belongs to the leave-one-out set exactly when it differs from the removed index."),
            TheoremNode("catalog-without-cardinality", "Catalog.without_card",
                "Leave-one-out cardinality", WithoutCardFormula(),
                "Erasing a member of the universal finite set subtracts exactly one from its cardinality."),
            TheoremNode("catalog-vector-lookup", "Catalog.theoremAt_ofVector",
                "Vector catalog lookup", VectorLookupFormula(),
                "Lookup in a vector-backed catalog reduces to the supplied vector function."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

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

    private static Formula AgreementFormula()
    {
        Formula realization = F.Id("r");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula readoutAgreement = Seq(
            Forall, Sp, i, Comma, Sp,
            Call("readout", realization, i, x), Sp, Eq, Sp,
            Call("readout", realization, i, y));
        Formula anchorAgreement = Seq(
            Forall, Sp, j, Comma, Sp, Open,
            x, Sp, Eq, Sp, Call("anchor", realization, j), Sp, Iff, Sp,
            y, Sp, Eq, Sp, Call("anchor", realization, j), Close);
        return Disp(Seq(
            Call("agrees", Call("toPrimitiveBundle", realization), x, y), Sp, Iff, Sp,
            Open, readoutAgreement, Close, Sp, Land, Sp, Open, anchorAgreement, Close, Dot));
    }

    private static Formula AdmitFormula() => Disp(Seq(
        Call("decide", Call("A", F.Id("a"))), Sp, Eq, Sp, F.Id("true"),
        Sp, Iff, Sp, Call("A", F.Id("a")), Dot));

    private static Formula WithoutMembershipFormula() => Disp(Seq(
        F.Id("candidate"), Sp, InMacro, Sp,
        Call("without", F.Id("catalog"), F.Id("removed")), Sp, Iff, Sp,
        F.Id("candidate"), Sp, Neq, Sp, F.Id("removed"), Dot));

    private static Formula WithoutCardFormula() => Disp(Seq(
        Call("card", Call("without", F.Id("catalog"), F.Id("i"))), Sp, Eq, Sp,
        Call("card", Call("Index", F.Id("catalog"))), Sp, Minus, Sp, D(1), Dot));

    private static Formula VectorLookupFormula() => Disp(Seq(
        Call("theoremAt", Call("ofVector", F.Id("units")), F.Id("i")), Sp, Eq, Sp,
        Call("units", F.Id("i")), Dot));
}
