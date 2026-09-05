using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class EulerPronyArithmeticRealizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Von Mangoldt Euler data generate exact finite Prony traces. The meromorphically "
            + "continued logarithmic derivative then maps each stored zeta-zero pole to a "
            + "golden Prony node with its multiplicity-derived residue weight.",
        H("Euler Data to Arithmetic Prony Nodes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("euler-mellin-node-is-the-standard-character"),
                DeclarationHandle.Create(Prefix + "euler_mellin_prony_node_eq_cpow"),
                H("Golden Euler nodes equal standard Mellin characters"),
                StatementSource.FromAuthor(MellinNodeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive integer address, the golden exponential of its normalized logarithmic coordinate is exactly the complex power n raised to minus the Mellin step.")),
                    Paragraph(Text(
                        "At unit step this specializes to the reciprocal integer node, while prime-power weights specialize through the canonical von Mangoldt formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-von-mangoldt-shifts-are-prony-traces"),
                DeclarationHandle.Create(Prefix + "finite_euler_shift_trace_eq_prony"),
                H("Finite von Mangoldt shift windows are exact Prony traces"),
                StatementSource.FromAuthor(ShiftTraceEqPronyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Sampling a finite von Mangoldt Dirichlet window along an arithmetic progression in the Mellin parameter factors into fixed base weights and powers of fixed Euler nodes.")),
                    Paragraph(Text(
                        "The right-hand side uses the repository's frozen crystal-time readout, so this bridge introduces no duplicate moment or delay-coordinate API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-euler-trace-is-the-standard-dirichlet-window"),
                DeclarationHandle.Create(
                    Prefix + "finite_euler_shift_trace_eq_vonMangoldt_dirichlet_window"),
                H("The Prony trace is the finite von Mangoldt Dirichlet window"),
                StatementSource.FromAuthor(DirichletWindowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive addresses, the same finite trace is written directly with the standard arithmetic terms Lambda(n) times n raised to the shifted negative Mellin parameter.")),
                    Paragraph(Text(
                        "This identifies the formal Prony nodes with genuine Euler characters rather than free spectral parameters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continued-euler-trace-agrees-on-the-euler-half-plane"),
                DeclarationHandle.Create(
                    Prefix + "continued_euler_trace_eq_single_address_heat_trace"),
                H("The continued Euler trace agrees with the von Mangoldt series"),
                StatementSource.FromAuthor(HalfPlaneAgreementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On real part greater than one, the negative logarithmic derivative of zeta is exactly the repository's von Mangoldt L-series.")),
                    Paragraph(Text(
                        "The logarithmic derivative supplies the canonical continuation used to locate the zero-side pole centers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continued-euler-trace-principal-part"),
                DeclarationHandle.Create(Prefix + "continued_euler_trace_principal_part"),
                H("Zeta multiplicity becomes the Euler-pole residue"),
                StatementSource.FromAuthor(PrincipalPartFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The analytic-unit factorization of a multiplicity-m zeta zero gives the punctured-neighborhood principal part minus m divided by s minus rho.")),
                    Paragraph(Text(
                        "The regular remainder is the logarithmic derivative of the analytic unit. Thus the pole center and residue weight are both arithmetic data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-data-euler-pole-golden-prony-realization"),
                DeclarationHandle.Create(
                    Prefix + "zero_data_euler_pole_golden_prony_realization"),
                H("Every stored Euler pole yields an actual golden Prony node"),
                StatementSource.FromAuthor(ZeroDataRealizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each canonical ZeroData entry carries a continued-Euler principal part, a nonzero golden exponential node, and a multiplicity-derived residue weight.")),
                    Paragraph(Text(
                        "Stored reflection inverts the node, and unit radius is equivalent to that zero lying on the critical line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-zero-pole-prony-window-observability"),
                DeclarationHandle.Create(
                    Prefix + "finite_zeta_pole_prony_window_injective"),
                H("Separated zero-pole nodes have exact finite observability"),
                StatementSource.FromAuthor(WindowInjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite family of distinct continued-Euler pole nodes is exactly observable from the first matching number of Prony moments through the frozen Vandermonde theorem.")),
                    Paragraph(Text(
                        "Node injectivity remains an explicit premise because one exponential sampling period can alias vertically separated frequencies."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula MellinNodeFormula()
    {
        Formula a = F.Id("a");
        Formula s = F.Id("s");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, D(0), Sp, Lt, Sp, a, Sp, Rightarrow, Sp, Forall, Sp, s, Comma, Sp,
            Call("eulerMellinPronyNode", a, s), Sp, Eq, Sp,
            a, Caret, Grp(Seq(Minus, s)), Dot));
    }

    private static Formula ShiftTraceEqPronyFormula()
    {
        Formula addr = F.Id("a");
        Formula b = F.Id("b");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula mode = F.Id("k");
        return Disp(Seq(
            Forall, Sp, addr, Comma, Sp, Forall, Sp, b, Comma, Sp, Forall, Sp, s, Comma, Sp, Forall, Sp, t, Comma, Sp,
            Call("finiteEulerShiftTrace", addr, b, s, t), Sp, Eq, Sp,
            Call("crystalTimeSample",
                Seq(mode, Sp, Mapsto, Sp, Call("eulerMellinPronyNode", Seq(addr, Open, mode, Close), s)),
                Seq(mode, Sp, Mapsto, Sp, Call("eulerMellinPronyWeight", Seq(addr, Open, mode, Close), b)),
                t), Dot));
    }

    private static Formula DirichletWindowFormula()
    {
        Formula addr = F.Id("a");
        Formula b = F.Id("b");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula mode = F.Id("k");
        Formula ak = Seq(addr, Open, mode, Close);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, addr, Comma, Sp,
            Open, Forall, Sp, mode, Comma, Sp, D(0), Sp, Lt, Sp, ak, Close, Sp, Rightarrow, Sp,
            Forall, Sp, b, Comma, Sp, Forall, Sp, s, Comma, Sp, Forall, Sp, t, Comma, RowBreak, Grp(),
            Call("finiteEulerShiftTrace", addr, b, s, t), Sp, Eq, Sp,
            Sum, Underscore, Grp(mode), Sp,
            Call("vonMangoldt", ak), Sp, Cdot, Sp,
            ak, Caret, Grp(Seq(Minus, Open, b, Sp, Plus, Sp, t, Sp, Cdot, Sp, s, Close)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula HalfPlaneAgreementFormula()
    {
        Formula s = F.Id("s");
        return Disp(Seq(
            Forall, Sp, s, Comma, Sp,
            D(1), Sp, Lt, Sp, Call("re", s), Sp, Rightarrow, Sp,
            Call("continuedEulerTrace", s), Sp, Eq, Sp,
            Call("singleAddressHeatTrace", s), Dot));
    }

    private static Formula PrincipalPartFormula()
    {
        Formula rho = F.Id("r");
        Formula m = F.Id("m");
        Formula u = F.Id("u");
        Formula z = F.Id("z");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, Comma, Sp, Forall, Sp, m, Comma, Sp,
            Call("hasZetaZeroMultiplicity", rho, m), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, u, Comma, Sp,
            Call("analyticAt", u, rho), Sp, Land, Sp,
            u, Open, rho, Close, Sp, Neq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Call("eventuallyEqNearPunctured", rho,
                F.Id("continuedEulerTrace"),
                Seq(z, Sp, Mapsto, Sp,
                    Minus, Frac, Grp(m), Grp(Seq(z, Sp, Minus, Sp, rho)),
                    Sp, Minus, Sp, Call("logDeriv", u, z))), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ZeroDataRealizationFormula()
    {
        Formula zd = F.Id("Z");
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula z = F.Id("z");
        Formula node = Call("zeroDataZetaPronyNode", zd, n);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, zd, Comma, Sp, Forall, Sp, n, Comma, RowBreak, Grp(),
            Open, Exists, Sp, u, Comma, Sp,
            Call("analyticAt", u, Call("zero", zd, n)), Sp, Land, Sp,
            u, Open, Call("zero", zd, n), Close, Sp, Neq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Call("eventuallyEqNearPunctured", Call("zero", zd, n),
                F.Id("continuedEulerTrace"),
                Seq(z, Sp, Mapsto, Sp,
                    Frac, Grp(Call("zeroDataEulerPoleWeight", zd, n)),
                        Grp(Seq(z, Sp, Minus, Sp, Call("zero", zd, n))),
                    Sp, Minus, Sp, Call("logDeriv", u, z))), Close,
            Sp, Land, RowBreak, Grp(),
            node, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Call("zeroDataZetaPronyNode", zd, Call("reflection", zd, n)), Sp, Eq, Sp,
            node, Caret, Grp(Seq(Minus, D(1))),
            Sp, Land, RowBreak, Grp(),
            Open,
            Call("norm", node), Sp, Eq, Sp, D(1), Sp, Iff, Sp,
            Call("re", Call("zero", zd, n)), Sp, Eq, Sp, F.Id("criticalAbscissa"),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula WindowInjectiveFormula()
    {
        Formula zd = F.Id("Z");
        Formula idx = F.Id("j");
        Formula mode = F.Id("k");
        Formula nodes = Seq(mode, Sp, Mapsto, Sp,
            Call("zeroDataZetaPronyNode", zd, Seq(idx, Open, mode, Close)));
        return Disp(Seq(
            Forall, Sp, zd, Comma, Sp, Forall, Sp, idx, Comma, Sp,
            Call("Injective", nodes), Sp, Rightarrow, Sp,
            Call("Injective", Call("firstCrystalTimeWindow", nodes)), Dot));
    }

}
