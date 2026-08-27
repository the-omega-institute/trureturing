using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class SpectrumCommitmentScopeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope."
            + "spectrum_commitment_atom_family_and_scope";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local DESC commitment has exactly five indexed atoms and the stated scope boundary.",
        H("Spectrum Commitment Atom Family and Scope"),
        Blocks(Describe.Lean(
            DescribeId.Create("spectrum-commitment-atom-family-and-scope"),
            DeclarationHandle.Create(Declaration),
            H("The five named DESC atoms have the exact local scope contract"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The construction instantiates the frozen seven-field SpectrumCommitment "
                        + "record. It supplies a finite atom family and scope predicate while "
                        + "leaving baseline, weight specification, and test plan explicit.")),
                Paragraph(Text(
                    "SpectrumAtom has the five named constructors T1 through T5. Its public "
                        + "index map is bijective onto Fin 5, so no theorem atom collides with "
                        + "or is omitted from the settlement positions.")),
                Paragraph(Text(
                    "Every named atom admits finite-language and countable-language scopes. "
                        + "The explicitly larger boundary-language scope is admitted exactly "
                        + "for T4, matching the countermodel exception without widening the "
                        + "main theorem domain.")),
                Paragraph(Text(
                    "A concrete Boolean computation witnesses that T4 admits the larger "
                        + "boundary scope while T1 does not, and Unit metadata instantiates "
                        + "the generic theorem."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula baselineType = F.Id("B");
        Formula weightType = F.Id("W");
        Formula planType = F.Id("P");
        Formula baseline = F.Id("b");
        Formula weight = F.Id("w");
        Formula plan = F.Id("p");
        Formula commitment = F.Id("K");
        Formula atom = F.Id("a");
        Formula atomType = F.Id("SpectrumAtom");
        Formula atomFamily = Call("atomFamily", commitment);
        Formula scopeAt(Formula subject, Formula scope) =>
            Call("scope", commitment, subject, scope);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, baselineType, Comma, Sp, weightType, Comma, Sp,
                planType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma),
            Seq(
                baseline, Colon, Sp, baselineType, Comma, Sp,
                weight, Colon, Sp, weightType, Comma, Sp,
                plan, Colon, Sp, planType, Comma),
            Seq(
                commitment, Sp, Eq, Sp,
                Call("descSpectrumCommitment", baseline, weight, plan), Comma),
            Seq(Call("card", atomFamily), Sp, Eq, Sp, D(5), Sp, Land),
            Seq(Call("Bijective", F.Id("index")), Sp, Land),
            Seq(
                Open, Forall, Sp, atom, Colon, Sp, atomType, Comma, Sp,
                atom, Sp, InMacro, Sp, atomFamily, Close, Sp, Land),
            Seq(
                Open, Forall, Sp, atom, Colon, Sp, atomType, Comma, Sp,
                scopeAt(atom, F.Id("finiteLanguage")), Sp, Eq, Sp, F.Id("true"),
                Sp, Land, Sp,
                scopeAt(atom, F.Id("countableLanguage")), Sp, Eq, Sp, F.Id("true"),
                Close, Sp, Land),
            Seq(
                scopeAt(F.Id("T4"), F.Id("largerBoundaryLanguage")),
                Sp, Eq, Sp, F.Id("true"), Sp, Land),
            Seq(
                Open, Forall, Sp, atom, Colon, Sp, atomType, Comma, Sp,
                scopeAt(atom, F.Id("largerBoundaryLanguage")), Sp, Eq, Sp,
                F.Id("true"), Sp, Iff, Sp, atom, Sp, Eq, Sp, F.Id("T4"),
                Close, Dot),
        ]));
    }
}
