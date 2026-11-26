using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class MarkedRibbonJointMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One joint quotient-moment portfolio for a literal marked signed ribbon.",
        H("One joint quotient-moment portfolio for a literal marked signed ribbon"),
        Blocks(Describe.Lean(DescribeId.Create("any-observable-joint-moments"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonJointMoments.any_observable_joint_moments"),
            H("A global physical readout for every joint ribbon-state observable"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The input is a finite flag carrier with fixed-point-free involutions for gaps and caps and disjoint marked four-flag bands. The graph components are exactly the quotient by gap moves, cap moves and literal band-end bridges. The proof restricts every matching action and every band to its own fibre and constructs a spanning-forest switch. The parity step shows that deleting one matching edge in either old boundary circle does not split its flag component, even when a cap equals a gap.")),
                Paragraph(Text("In each component, a numbered alternating flag orbit gives an actual signed bouquet. The intrinsic binary labels are chord classes modulo the radical of the signed pairing. Embed each component's labels in the global direct sum at its own coordinate. Projection of a selected global column span is exactly the corresponding selected local span; this, not a multiplication of previously evaluated local readouts, carries the component loop charges through a single global subspace-lattice reconstruction.")),
                Paragraph(Text("One family of physical diagonal mixed code marginal moments, indexed by quotient spaces of the fixed joint label space, and of order one plus its dimension, suffices for every assignment at a fixed nonzero real loop value. The chart and switch are chosen independently of the loop value. Coefficients can depend on the loop value but are fixed before the state or observable. The explicit count prefactor is the loop value to the number of components plus the selected bands. Any real-valued joint observable may weight the resulting sum, including nonfactorizing correlations between components.")),
                Paragraph(Text("This covers disconnected, twisted, empty and zero-band flag models. Vertices with no flags are not modeled. It is neither a claim about full Jones normalization nor a claim about the number of quotient measurements or computational complexity. Partial duality and spanning-tree bouquet reduction are classical (Chmutov, JCTB 99 (2009), 617–638, arXiv:0711.3490); the new endpoint is their literal finite-flag bridge to one global physical quotient-code portfolio."))),
            DescribeRole.Theorem))));
    private static Formula Bind(FormulaQuantifier q, string n, Formula t, Formula b) =>
        new Formula.Bind(q, FormulaIdentifier.Create(n), t, b);
    private static Formula All(string n, Formula t, Formula b) => Bind(FormulaQuantifier.ForAll, n, t, b);
    private static Formula Ex(string n, Formula t, Formula b) => Bind(FormulaQuantifier.Exists, n, t, b);
    private static Formula Statement()
    {
        var r = F.Id("R"); var c = F.Id("C"); var d = F.Id("d");
        var a = F.Id("alpha"); var w = F.Id("w");
        return Disp(All("R",Call("FiniteLiteralMarkedSignedRibbons"),
            Ex("C",Call("ExtractedChartsWithStateBijection",r),
                All("d",Call("NonzeroReals"),
                    Ex("alpha",Call("JointQuotientMomentCoefficients",c),
                        All("w",Call("RealJointStateObservables",r),
                            Equal(Call("LiteralWeightedCircleSum",r,d,w),
                                  Call("NormalizedJointMomentSum",r,c,d,a,w))))))));
    }
}
