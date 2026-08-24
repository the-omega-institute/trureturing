using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class NormalizedHiddenAddressConservationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized streamline addresses are conserved on connected time segments.",
        H("Normalized Hidden-Address Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-hidden-address-conservation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/NormalizedHiddenAddressConservation."
                        + "normalized_streamline_hidden_address_conservation"),
                H("Connected streamline segments conserve their hidden address"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A continuous universal-solenoid history has unique normalized "
                            + "streamline data: a continuous real lift fixed by the repository's "
                            + "base representative and a hidden kernel coordinate.")),
                    Paragraph(Text(
                        "The canonical hidden coordinate is constant at any two times in every "
                            + "preconnected segment. This applies the imported normalized "
                            + "streamline construction and its throat-component computation.")),
                    Paragraph(Text(
                        "The second public clause treats an arbitrary proposed hidden offset "
                            + "under the same normalized visible lift. If it gives different "
                            + "addresses at two times in a preconnected segment, the imported "
                            + "nonconstant-offset theorem rules out continuity on that segment.")),
                    Paragraph(Text(
                        "The earlier conditional streamline theorem explicitly left normalized "
                            + "existence and canonicity open. The imported family construction "
                            + "supplies those obligations here, so this module contributes only "
                            + "the bridge joining construction, conservation, and obstruction."))),
                DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula path = F.Id("x");
        Formula lift = F.Id("a");
        Formula address = F.Id("k");
        Formula candidate = Kappa;
        Formula segment = F.Id("I");
        Formula time = F.Id("t");
        Formula first = new Formula.Subscript(time, D(0));
        Formula second = new Formula.Subscript(time, D(1));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula solenoid = new Formula.Subscript(Sigma, Infty);
        Formula hiddenKernel = Seq(Ker, Open, Pi, Close);
        Formula hiddenAtPath = new Formula.Subscript(address, path);
        Formula pathAt = Seq(path, Open, time, Close);
        Formula liftAt = Seq(lift, Open, time, Close);
        Formula candidateAt = Seq(candidate, Open, time, Close);
        Formula reconstructed = Seq(
            pathAt, Sp, Eq, Sp, Call("realFlow", liftAt), Sp, Plus, Sp, address);
        Formula candidateReconstructed = Seq(
            pathAt, Sp, Eq, Sp, Call("realFlow", liftAt), Sp, Plus, Sp,
            candidateAt);
        Formula normalization = Seq(
            lift, Open, D(0), Close, Sp, Eq, Sp,
            Call("base", Seq(path, Open, D(0), Close)));
        Formula conservation = Seq(
            Forall, Sp, segment, Comma, Sp, Call("IsPreconnected", segment),
            Comma, Sp, Forall, Sp, first, Comma, Sp, second, InMacro, Sp,
            segment, Comma, Sp,
            hiddenAtPath, Open, first, Close, Sp, Eq, Sp,
            hiddenAtPath, Open, second, Close);
        Formula uniqueNormalized = Seq(
            Exists, Bang, Sp, Open, lift, Comma, Sp, address, Close,
            Colon, Sp, Call("ContinuousMaps", reals, reals),
            Sp, Times, Sp, hiddenKernel,
            Comma, Sp, normalization, Sp, Land, Sp,
            Open, Forall, Sp, time, Comma, Sp, reconstructed, Close,
            Sp, Land, Sp, conservation);
        Formula candidatePremises = Seq(
            normalization, Sp, Land, Sp, Call("IsPreconnected", segment),
            Sp, Land, Sp, first, Comma, Sp, second, InMacro, Sp, segment,
            Sp, Land, Sp, Open, Forall, Sp, time, InMacro, Sp, segment,
            Comma, Sp, candidateReconstructed, Close, Sp, Land, Sp,
            candidate, Open, first, Close, Sp, Neq, Sp,
            candidate, Open, second, Close);
        Formula obstruction = Seq(
            Forall, Sp, lift, Comma, Sp, candidate, Comma, Sp, segment,
            Comma, Sp, first, Comma, Sp, second, Comma, Sp,
            Open, candidatePremises, Close, Sp, Rightarrow, Sp, Neg,
            Call("ContinuousOn", candidate, segment));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, path, Colon, Sp, Call("Continuous", Seq(
                reals, Sp, To, Sp, solenoid)), Comma,
            RowBreak, Grp(),
            Open, uniqueNormalized, Close, Sp, Land, RowBreak, Grp(),
            Open, obstruction, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
