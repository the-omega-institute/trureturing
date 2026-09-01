using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylDisplacementTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weyl displacement words have trace M at the zero index and zero trace elsewhere; "
            + "their trace pairings are M at equal indices and zero otherwise.",
        H("Trace Pairings for Weyl Displacement Words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weyl-displacement-trace-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementTrace."
                        + "displacement_trace_eq_zero"),
                H("Vanishing trace away from the origin"),
                StatementSource.FromAuthor(TraceZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A displacement word has zero trace whenever at least one of its two "
                            + "residue indices is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-trace-origin"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementTrace."
                        + "displacement_trace_origin"),
                H("Trace at the origin"),
                StatementSource.FromAuthor(TraceOriginFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At the zero index, the trace of the displacement word is the window "
                            + "cardinality M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace"),
                H("Trace of a displacement word"),
                StatementSource.FromAuthor(TraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The trace of a displacement word is M when both residue indices vanish "
                            + "and zero otherwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-displacement-trace-orthogonal"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/WeylDisplacementTrace."
                        + "displacement_trace_orthogonal"),
                H("Pairwise orthogonality for the trace form"),
                StatementSource.FromAuthor(TraceOrthogonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The trace pairing of two displacement words is M when their two residue "
                            + "indices agree and zero otherwise; hence distinct indices are "
                            + "orthogonal for this trace form.")),
                    Paragraph(Text(
                        "This is the pairing identity itself. This module proves no conclusion "
                            + "about linear independence, spanning, or a basis, and it must not "
                            + "be read as asserting any such conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Displacement(Formula window, Formula first, Formula second) =>
        Call("displacement", window, first, second);

    private static Formula Trace(Formula matrix) => Call("trace", matrix);

    private static Formula ComplexCast(Formula value) =>
        Grp(value, Colon, Sp, Mathbb, Grp(F.Id("C")));

    private static Formula WindowContext(Formula window) =>
        Seq(
            Forall, Sp, window, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NeZero")), Open, window, Close,
            CloseBracket, Comma, Esc);

    private static Formula Residues(Formula window, params Formula[] names)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var index = 0; index < names.Length; index += 1)
        {
            items.Add(names[index]);
            if (index + 1 < names.Length)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
        }

        items.Add(Colon);
        items.Add(Sp);
        items.Add(Operatorname);
        items.Add(Grp(F.Id("ZMod")));
        items.Add(Open);
        items.Add(window);
        items.Add(Close);
        items.Add(Comma);
        items.Add(Esc);
        return Seq([.. items]);
    }

    private static Formula TraceZeroFormula()
    {
        Formula m = F.Id("M");
        Formula e = F.Id("e");
        Formula f = F.Id("f");
        Formula zero = Num(0);

        return Disp(Seq(
            WindowContext(m),
            Residues(m, e, f),
            Grp(e, Sp, Neq, Sp, zero, Sp, Lor, Sp, f, Sp, Neq, Sp, zero), Sp,
            Implies, Sp,
            Trace(Displacement(m, e, f)), Sp, Eq, Sp, zero, Dot));
    }

    private static Formula TraceOriginFormula()
    {
        Formula m = F.Id("M");
        Formula zero = Num(0);

        return Disp(Seq(
            WindowContext(m),
            Trace(Displacement(m, zero, zero)), Sp, Eq, Sp, ComplexCast(m), Dot));
    }

    private static Formula TraceFormula()
    {
        Formula m = F.Id("M");
        Formula e = F.Id("e");
        Formula f = F.Id("f");
        Formula zero = Num(0);

        return Disp(Seq(
            WindowContext(m),
            Residues(m, e, f),
            Trace(Displacement(m, e, f)), Sp, Eq, Sp,
            Begin, Grp(F.Id("cases")),
            ComplexCast(m), Comma, Amp,
            e, Sp, Eq, Sp, zero, Sp, Land, Sp, f, Sp, Eq, Sp, zero, RowBreak,
            zero, Comma, Amp, F.Text, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")), Dot));
    }

    private static Formula TraceOrthogonalFormula()
    {
        Formula m = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula zero = Num(0);

        return Disp(Seq(
            WindowContext(m),
            Residues(m, a, b, c, d),
            Trace(Seq(
                Call("star", Displacement(m, a, b)), Sp, Cdot, Sp,
                Displacement(m, c, d))), Sp, Eq, Sp,
            Begin, Grp(F.Id("cases")),
            ComplexCast(m), Comma, Amp,
            a, Sp, Eq, Sp, c, Sp, Land, Sp, b, Sp, Eq, Sp, d, RowBreak,
            zero, Comma, Amp, F.Text, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")), Dot));
    }
}
