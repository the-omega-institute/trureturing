using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class CompactCharacterMellinObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/CompactCharacterMellinObstruction."
            + "compact_character_modulus_and_mellin_obstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous complex characters on compact groups have unit modulus, so a Mellin "
            + "mode with nonzero real drift cannot descend through a Pontryagin character.",
        H("Compact Character Modulus and Mellin Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-character-modulus-and-mellin-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("Compact characters exclude nonzero Mellin drift"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier G is an arbitrary compact topological group. A continuous "
                        + "homomorphism from G to the units of the complex numbers is bounded "
                        + "on its compact source; applying the same bound to every positive "
                        + "power and to the inverse forces unit norm.")),
                Paragraph(Text(
                    "The second public conjunct uses the canonical repository Mellin "
                        + "character. If it factored through a Pontryagin character, every "
                        + "value would lie on the complex unit circle, contradicting the "
                        + "exact frozen criterion when the real drift delta is nonzero.")),
                Paragraph(Text(
                    "The no-factorization statement quantifies the descent map, phase "
                        + "character, drift, frequency, and time; it does not replace the "
                        + "source character by an abstract unitary predicate."))),
            DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula group = F.Id("G");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula complexUnits = Call("Units", complex);
        Formula logScale = Call("Multiplicative", real);
        Formula chi = F.Id("chi");
        Formula element = F.Id("g");
        Formula delta = DeltaLower;
        Formula gamma = GammaLower;
        Formula descent = F.Id("descent");
        Formula phase = F.Id("phase");
        Formula time = F.Id("t");

        Formula carrierAssumptions = Seq(
            Call("Group", group), Sp, Land, Sp,
            Call("TopologicalSpace", group), Sp, Land, Sp,
            Call("IsTopologicalGroup", group), Sp, Land, Sp,
            Call("CompactSpace", group));

        Formula modulusClause = Seq(
            Forall, Sp, chi, Colon, Sp,
            Call("ContinuousMonoidHom", group, complexUnits), Comma, Sp,
            Forall, Sp, element, Sp, InMacro, Sp, group, Comma, Sp,
            new Formula.Norm(Call("coe", Call(chi, element))), Sp, Eq, Sp, D(1));

        Formula exponent = Seq(
            Call("coe", delta), Sp, Plus, Sp,
            F.Id("i"), Sp, Cdot, Sp, Call("coe", gamma));
        Formula logTime = Call("ofAdd", time);
        Formula mellinValue = Call("mellinCharacter", exponent, logTime);
        Formula descendedTime = Call(descent, logTime);
        Formula phaseValue = Call("coe", Call(phase, descendedTime));
        Formula factorization = Seq(
            Forall, Sp, time, Sp, InMacro, Sp, real, Comma, Sp,
            mellinValue, Sp, Eq, Sp, phaseValue);
        Formula obstructionClause = Seq(
            Forall, Sp, delta, Comma, Sp, gamma, Sp, InMacro, Sp, real, Comma, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, descent, Colon, Sp,
            Call("ContinuousMonoidHom", logScale, group), Comma, Sp,
            phase, Colon, Sp, Call("PontryaginDual", group), Comma, Sp,
            new Formula.Not(factorization));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, RowBreak, Grp(),
            carrierAssumptions, Sp, Rightarrow, RowBreak, Grp(),
            Open, modulusClause, Close, Sp, Land, RowBreak, Grp(),
            Open, obstructionClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
