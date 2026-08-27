using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ObserverRefinementVisibleResidualEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/ObserverRefinementVisibleResidualEquivalence."
            + "observer_refinement_visible_residual_equivalence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical observer refinement is dual to visible and residual subspace inclusion.",
        H("Observer Refinement, Visibility, and Residuals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-refinement-visible-residual-equivalence"),
                DeclarationHandle.Create(Declaration),
                H("Observer refinement has dual visible and residual criteria"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each observer signature is constructed from real Hilbert--Schmidt "
                            + "pairings between density-state matrices and its Hermitian "
                            + "effect family. Its visible space is the real span of the "
                            + "identity and those effects, and its residual is the orthogonal "
                            + "complement of that span.")),
                    Paragraph(Text(
                        "Refinement means that equality of the second observer's signature "
                            + "on two physical density states forces equality of the first. "
                            + "Perturbations around the maximally mixed state turn every "
                            + "residual direction into a difference of density states.")),
                    Paragraph(Text(
                        "Consequently refinement is exactly reverse inclusion of residuals. "
                            + "The pinned orthogonal-complement order theorem then identifies "
                            + "that condition with forward inclusion of visible spaces."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula indexOne = F.Id("IndexOne");
        Formula indexTwo = F.Id("IndexTwo");
        Formula effectsOne = F.Id("effectsOne");
        Formula effectsTwo = F.Id("effectsTwo");
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula stateOperator = F.Id("stateOperator");
        Formula signatureOne = F.Id("signatureOne");
        Formula signatureTwo = F.Id("signatureTwo");
        Formula visibleOne = F.Id("visibleOne");
        Formula visibleTwo = F.Id("visibleTwo");
        Formula residualOne = F.Id("residualOne");
        Formula residualTwo = F.Id("residualTwo");
        Formula refines = F.Id("refines");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("HermitianSpace", d);
        Formula density = Call("DensityState", Call("Fin", d));
        Formula State(Formula state) => Call("stateOperator", state);
        Formula SignatureOne(Formula state) => Call("signatureOne", state);
        Formula SignatureTwo(Formula state) => Call("signatureTwo", state);
        Formula Visible(Formula effects) =>
            Call("span", real,
                Call("insert", Call("identityHermitian", d), Call("range", effects)));
        Formula Orthogonal(Formula subspace) => Call("orthogonal", subspace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, d, Colon, Sp, F.Id("Nat"), Comma, Sp,
                Call("NeZero", d), Comma, Sp,
                indexOne, Comma, Sp, indexTwo, Colon, Sp,
                Operatorname, Grp(F.Id("Type")), Comma),
            Seq(
                effectsOne, Colon, Sp, indexOne, Sp, To, Sp, carrier, Comma, Sp,
                effectsTwo, Colon, Sp, indexTwo, Sp, To, Sp, carrier, Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                stateOperator, Colon, Sp, density, Sp, To, Sp, carrier,
                Sp, Colon, Eq, Sp, Rho, Sp, Mapsto, Sp,
                Call("HermitianMk", Call("ofMatrixSymm", Call("val", rho))), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                signatureOne, Sp, Colon, Eq, Sp, Rho, Sp, Mapsto, Sp,
                F.Id("i"), Sp, Mapsto, Sp,
                Call("innerR", State(rho), Call("effectsOne", F.Id("i"))), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                signatureTwo, Sp, Colon, Eq, Sp, Rho, Sp, Mapsto, Sp,
                F.Id("i"), Sp, Mapsto, Sp,
                Call("innerR", State(rho), Call("effectsTwo", F.Id("i"))), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                visibleOne, Sp, Colon, Eq, Sp, Visible(effectsOne), Comma, Sp,
                visibleTwo, Sp, Colon, Eq, Sp, Visible(effectsTwo), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                residualOne, Sp, Colon, Eq, Sp, Orthogonal(visibleOne), Comma, Sp,
                residualTwo, Sp, Colon, Eq, Sp, Orthogonal(visibleTwo), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                refines, Sp, Colon, Eq, Sp,
                Forall, Sp, rho, Comma, Sp, sigma, Colon, Sp, density, Comma, Sp,
                SignatureTwo(rho), Sp, Eq, Sp, SignatureTwo(sigma),
                Sp, Rightarrow, Sp,
                SignatureOne(rho), Sp, Eq, Sp, SignatureOne(sigma), Comma),
            Seq(
                Open, refines, Sp, Iff, Sp,
                residualTwo, Sp, Subseteq, Sp, residualOne, Close,
                Sp, Land, Sp),
            Seq(
                Open, residualTwo, Sp, Subseteq, Sp, residualOne,
                Sp, Iff, Sp, visibleOne, Sp, Subseteq, Sp, visibleTwo, Close, Dot),
        ]));
    }
}
