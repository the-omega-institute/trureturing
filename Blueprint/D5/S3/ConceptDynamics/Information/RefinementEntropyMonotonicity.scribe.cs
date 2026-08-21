using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class RefinementEntropyMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement increases concept information and decreases residual entropy.",
        H("Concept Entropy under Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-information-residual-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Information/RefinementEntropyMonotonicity."
                        + "refinement_information_residual_monotone"),
                H("Refinement increases information and decreases residual entropy"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let mu be a normalized nonnegative mass function on a finite state "
                            + "carrier. Concept information is the Shannon entropy of the "
                            + "readout pushforward, while concept residual is the conditional "
                            + "entropy of the source state given that readout.")),
                    Paragraph(Text(
                        "Both laws are constructed from mu and the canonical concept readouts. "
                            + "Refinement uses the family factorization relation: the coarse "
                            + "readout is obtained by deterministically forgetting the fine one.")),
                    Paragraph(Text(
                        "The displayed information and residual inequalities are separate public "
                            + "conjuncts. The proof directly applies the frozen deterministic "
                            + "pushforward entropy classification and then the finite entropy "
                            + "chain rule to the graph-supported readout laws."))),
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

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula MonotonicityFormula()
    {
        Formula state = F.Id("X");
        Formula coarseCarrier = F.Id("C");
        Formula fineCarrier = F.Id("D");
        Formula mu = F.Id("mu");
        Formula x = F.Id("x");
        Formula coarse = new Formula.Subscript(F.Id("q"), coarseCarrier);
        Formula fine = new Formula.Subscript(F.Id("q"), fineCarrier);
        Formula mux = Seq(mu, Open, x, Close);
        Formula probabilityLaw = Seq(
            Open, Forall, Sp, x, Comma, Sp, D(0), Sp, Leq, Sp, mux, Close,
            Sp, Land, Sp, Sum, Underscore, Grp(x), Sp, mux, Sp, Eq, Sp, D(1));
        Formula informationCoarse = Call("conceptInformation", mu, coarse);
        Formula informationFine = Call("conceptInformation", mu, fine);
        Formula residualCoarse = Call("conceptResidual", mu, coarse);
        Formula residualFine = Call("conceptResidual", mu, fine);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coarseCarrier, Comma, Sp, fineCarrier,
            Comma, RowBreak, Grp(),
            Fintype(state), Sp, Fintype(coarseCarrier), Sp, Fintype(fineCarrier),
            Comma, RowBreak, Grp(),
            mu, Colon, Sp, state, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma,
            RowBreak, Grp(),
            coarse, Colon, Sp, state, Sp, To, Sp, coarseCarrier, Comma, Sp,
            fine, Colon, Sp, state, Sp, To, Sp, fineCarrier, Comma,
            RowBreak, Grp(),
            Open, probabilityLaw, Close, Sp, Land, Sp,
            Call("Refines", coarse, fine), Sp, Rightarrow, RowBreak, Grp(),
            Open, informationCoarse, Sp, Leq, Sp, informationFine, Close,
            Sp, Land, RowBreak, Grp(),
            Open, residualFine, Sp, Leq, Sp, residualCoarse, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
