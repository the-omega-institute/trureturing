using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiniteInputGeneratorPeriodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite deterministic input generator makes every extended orbit eventually periodic.",
        H("Finite Input Generator Periodicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-input-generators-give-eventually-periodic-product-orbits"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity."
                    + "finite_input_generator_eventually_periodic"),
                H("Finite input generators give eventually periodic product orbits"),
                StatementSource.FromAuthor(PeriodicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state carrier and C a finite deterministic input "
                            + "generator with transition J and output g into the input type U. "
                            + "For an input-indexed update F, the displayed self-map sends "
                            + "(y,c) to (F(g(c))(y),J(c)) on Y times C.")),
                    Paragraph(Text(
                        "For every initial product state there are a tail index mu and a "
                            + "strictly positive period p such that all iterates after mu agree "
                            + "when shifted by p. This is the eventual periodicity of the whole "
                            + "extended trajectory, not merely a repeated pair of states.")),
                    Paragraph(Text(
                        "The exact pinned-library hit Finite.exists_ne_map_eq_of_infinite gives "
                            + "two equal states in the orbit map from the naturals to the finite "
                            + "product carrier and is imported and applied. Loogle also found "
                            + "EquivFin.not_injective_infinite_finite. LeanSearch returned the "
                            + "nearby injective-map periodic-points lemma, which does not apply "
                            + "to arbitrary updates, and no exact theorem. Repository and "
                            + "formalization searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ProductUpdate(Formula y, Formula c) =>
        Seq(Open, Apply(Apply(F.Id("F"), Apply(F.Id("g"), c)), y), Comma, Sp,
            Apply(F.Id("J"), c), Close);

    private static Formula Iterate(Formula exponent, Formula initial) =>
        Seq(Open, Open, F.Id("y"), Comma, Sp, F.Id("c"), Close, Sp, Mapsto, Sp,
            ProductUpdate(F.Id("y"), F.Id("c")), Close,
            Caret, Grp(exponent), Open, initial, Close);

    private static Formula PeriodicityFormula()
    {
        Formula mu = F.Id("mu");
        Formula period = F.Id("p");
        Formula time = F.Id("t");
        Formula initial = Seq(F.Id("z"), Underscore, Grp(D(0)));
        return Disp(Seq(
            Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("C"), Comma, Sp, F.Id("U"), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Open, F.Id("Y"), Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Open, F.Id("C"), Close,
            CloseBracket, Comma, Esc,
            F.Id("F"), Colon, Sp, F.Id("U"), Sp, To, Sp, F.Id("Y"), Sp, To, Sp,
            F.Id("Y"), Comma, Sp,
            F.Id("J"), Colon, Sp, F.Id("C"), Sp, To, Sp, F.Id("C"), Comma, Sp,
            F.Id("g"), Colon, Sp, F.Id("C"), Sp, To, Sp, F.Id("U"), Comma, Esc,
            Forall, Sp, initial, InMacro, Sp, F.Id("Y"), Times, Sp, F.Id("C"), Comma, Esc,
            Exists, Sp, mu, Comma, Sp, period, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            Forall, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Iterate(Seq(mu, Plus, time, Plus, period), initial), Sp, Eq, Sp,
            Iterate(Seq(mu, Plus, time), initial), Dot));
    }
}
