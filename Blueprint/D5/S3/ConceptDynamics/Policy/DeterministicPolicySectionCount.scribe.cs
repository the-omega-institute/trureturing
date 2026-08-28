using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class DeterministicPolicySectionCountDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Policy/DeterministicPolicySectionCount."
            + "deterministic_policy_sections_lower_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct public states with at least two legal actions force exponentially many deterministic sections.",
        H("Deterministic Policy Section Count"),
        Blocks(Describe.Lean(
            DescribeId.Create("deterministic-policy-sections-lower-bound"),
            DeclarationHandle.Create(Declaration),
            H("Legal deterministic sections have an exponential lower bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The legal-action relation is the source primitive: every public state has "
                        + "a finite nonempty legal-action fiber. A deterministic section is the "
                        + "dependent product that assigns one subtype element to every public state.")),
                Paragraph(Text(
                    "An injectively selected family of k public states has at least two choices "
                        + "in each corresponding fiber. The finite product cardinality theorem "
                        + "therefore gives the lower bound 2^k, while the remaining nonempty fibers "
                        + "can only increase the full section-space cardinality.")),
                Paragraph(Text(
                    "The proof uses the exact finite-cardinality and product-order lemmas from "
                        + "pinned Mathlib; no Boolean-only or target-shaped section object is introduced."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula SetOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Set")), Open, type, Close);

    private static Formula Subtype(Formula element, Formula predicate) =>
        Seq(OpenBrace, element, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula qType = F.Id("Q");
        Formula actionType = F.Id("A");
        Formula k = F.Id("k");
        Formula legal = F.Id("legal");
        Formula selected = F.Id("selected");
        Formula q = F.Id("q");
        Formula i = F.Id("i");
        Formula action = F.Id("a");
        Formula finK = Call("Fin", k);
        Formula finitePremises = Seq(
            Call("Finite", qType), Sp, Land, Sp,
            Call("Finite", actionType), Sp, Land, Sp,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("q"),
                qType,
                Call("Nonempty", Apply(legal, q))), Sp, Land, Sp,
            Call("Injective", selected), Sp, Land, Sp,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("i"),
                finK,
                    Seq(D(2), Sp, Leq, Sp,
                    Card(Subtype(action, Seq(action, Sp, InMacro,
                        Sp, Apply(legal, Apply(selected, i))))))));
        Formula selectedType = Arrow(finK, qType);
        Formula sectionsType = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("q"),
            qType,
            Subtype(action, Seq(action, Sp, InMacro, Sp, Apply(legal, q))));
        Formula conclusion = Seq(D(2), Caret, Grp(k), Sp, Leq, Sp,
            Card(sectionsType));

        return Disp(Seq(
            Forall, Sp, qType, Comma, Sp, actionType, Comma, Sp, k,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            legal, Colon, Sp, Arrow(qType, SetOf(actionType)), Comma, Sp,
            selected, Colon, Sp, selectedType, Comma, RowBreak, Grp(),
            finitePremises, Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
