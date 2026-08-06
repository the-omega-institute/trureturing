using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class EulerWindowsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef HedenmalmHilbert =
        LibraryNoteRef.Create("D5/L/hedenmalm1997hilbert");
    private static readonly LibraryNoteRef ApostolEuler =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/EulerWindows",
            "The prime-axis coordinate trace agrees with zeta in its convergence domain, while finite prime windows stay zero-free."),
        H("Euler Windows Below the Completed Zero Reading"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-prime-axis-heat-trace-is-the-coordinate-sum"),
                H("The prime-axis heat trace is the coordinate sum"),
                LeanDefinition(
                    "D5/S3/Zeros/EulerWindows.primeAxisHeatTrace"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(
                    Text("The definition sums the existing labeled-zeta coefficient over the repository's PrimeAxisTable. The table type and coefficient family already exist; this declaration proves neither convergence nor a spectral trace-class realization. "),
                    Ref("D5/L/hedenmalm1997hilbert"),
                    Text(" supplies the square-summable Dirichlet-series context, but the prime-axis encoding and heat-trace name are repository translations. This is the initial half-plane reading that an O-6 route must connect faithfully to completed zeta.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-prime-axis-heat-trace-equals-classical-zeta-in-the-absolute-half-plane"),
                H("The prime-axis heat trace equals classical zeta in the absolute half-plane"),
                LeanTheorem(
                    "D5/S3/Zeros/EulerWindows.prime_axis_heat_trace_eq_zeta"),
                In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, D(1), Lt, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("primeAxisHeatTrace")), Open, F.Id("s"), Close, Eq, Operatorname, Grp(F.Id("classicalZeta")), Open, F.Id("s"), Close)),
                DescribeProvenance.LiteratureAttested(HedenmalmHilbert),
                Blocks(Paragraph(Text(
                    "For real part strictly greater than one, the PrimeAxisTable coefficient sum is classical zeta. The half-plane hypothesis is explicit and supplies the convergence needed by the existing zeta-kernel theorem. Compared with the ingested definition, the checked statement uses the repository's established coefficient family and asserts no analytic continuation beyond this domain. It is the local-germ endpoint that continuation uniqueness can eventually join to the completed reading on the O-6 path.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-prime-windows-have-no-zeros-at-positive-abscissa"),
                H("Finite prime windows have no zeros at positive abscissa"),
                LeanTheorem(
                    "D5/S3/Zeros/EulerWindows.finite_euler_window_ne_zero"),
                Disp(Seq(Forall, Sp, F.Id("S"), Subset, Underscore, Grp(Operatorname, Grp(F.Id("fin"))), Mathbb, Grp(F.Id("N")), Comma, Esc, Open, Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("S"), Comma, Esc, Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Close, Sp, Rightarrow, Sp, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, D(0), Lt, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("finiteEulerProduct")), Open, F.Id("S"), Comma, F.Id("s"), Close, Neq, Sp, D(0))),
                DescribeProvenance.LiteratureAttested(ApostolEuler),
                Blocks(Paragraph(Text(
                    "For a supplied finite set of natural numbers, a supplied proof that every member is prime, and a complex parameter with positive real part, the corresponding finite Euler product is nonzero. A finite set is always inhabited as a value, but it may be empty; no nonempty window is required. Compared with the ingested corollary, Lean proves only finite-window nonvanishing. It does not prove all-prime tail participation, critical-strip convergence failure, epsilon-readout necessity, window escape, or a continued-correlation interpretation. For O-6 this excludes finite Euler factors as the source of a projected zero while leaving the analytic tail and continuation obligations open.")))
            )),
[
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Zeros/EulerWindows.finite_euler_window_ne_zero")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Zeros/EulerWindows.primeAxisHeatTrace")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Zeros/EulerWindows.prime_axis_heat_trace_eq_zeta")),
                    DocumentEdge.Dependency.Create(
                        GidRef.Create("D5/S3/Weil/EulerProduct")),
                    DocumentEdge.Dependency.Create(
                        GidRef.Create("D5/S3/Weil/SpectralHilbert")),
                ]));
}
