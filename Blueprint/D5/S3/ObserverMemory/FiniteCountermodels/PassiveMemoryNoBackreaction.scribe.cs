using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class PassiveMemoryNoBackreactionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Passive triangular memory stores order without changing scalar spectral invariants.",
        H("Passive Memory No-Backreaction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("passive-memory-adjacent-swap-holonomy-formula"),
                DeclarationHandle.Create(Prefix + "memory_holonomy_formula"),
                H("The adjacent-swap defect is explicitly off-diagonal"),
                StatementSource.FromAuthor(MemoryHolonomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary complex memory update F, injection scale v, and "
                            + "readouts Lp and Lq, reversing the two prime-memory factors "
                            + "produces the displayed matrix with only its upper-right entry "
                            + "potentially nonzero.")),
                    Paragraph(Text(
                        "The formula identifies the defect exactly as "
                            + "(Lq - Lp)(F - 1)v. It does not assert that every adjacent swap "
                            + "is nontrivial, since that scalar can vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-holonomy-has-zero-trace"),
                DeclarationHandle.Create(Prefix + "memory_holonomy_trace_zero"),
                H("The adjacent-swap defect has zero trace"),
                StatementSource.FromAuthor(MemoryHolonomyTraceZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every complex choice of F, v, Lp, and Lq, the trace of the "
                            + "adjacent-swap memory holonomy is zero. This follows from the "
                            + "zero diagonal in the explicit defect matrix.")),
                    Paragraph(Text(
                        "Trace blindness is only a scalar invariant statement. It does not "
                            + "make the holonomy matrix zero or rule out a nonzero off-diagonal "
                            + "record of order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-holonomy-has-zero-determinant"),
                DeclarationHandle.Create(Prefix + "memory_holonomy_det_zero"),
                H("The adjacent-swap defect has zero determinant"),
                StatementSource.FromAuthor(MemoryHolonomyDetZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every complex choice of F, v, Lp, and Lq, the determinant of "
                            + "the adjacent-swap memory holonomy is zero. The explicit defect "
                            + "is strictly upper triangular.")),
                    Paragraph(Text(
                        "A zero determinant records singularity, not equality with the zero "
                            + "matrix. The theorem therefore remains compatible with a nonzero "
                            + "off-diagonal order defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-trace-is-injection-invariant"),
                DeclarationHandle.Create(Prefix + "passive_memory_trace_invariant"),
                H("Changing the passive injection preserves trace"),
                StatementSource.FromAuthor(PassiveMemoryTraceInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At fixed complex diagonal entries F and L, replacing injection B1 "
                            + "by B2 leaves the trace of the passive memory matrix unchanged. "
                            + "Only the upper-right entry varies.")),
                    Paragraph(Text(
                        "The equality is restricted to changes of the injection coordinate. "
                            + "It makes no invariance claim when either diagonal entry F or L "
                            + "is changed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-determinant-is-injection-invariant"),
                DeclarationHandle.Create(Prefix + "passive_memory_det_invariant"),
                H("Changing the passive injection preserves determinant"),
                StatementSource.FromAuthor(PassiveMemoryDetInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At fixed complex diagonal entries F and L, replacing injection B1 "
                            + "by B2 leaves the determinant of the passive memory matrix "
                            + "unchanged. The determinant depends only on the diagonal.")),
                    Paragraph(Text(
                        "This is an injection-blind scalar invariant, not an equality of the "
                            + "two matrices. Distinct upper-right entries can still encode "
                            + "different memory data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-charpoly-is-injection-invariant"),
                DeclarationHandle.Create(Prefix + "passive_memory_charpoly_invariant"),
                H("Changing the passive injection preserves the characteristic polynomial"),
                StatementSource.FromAuthor(PassiveMemoryCharpolyInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At fixed complex diagonal entries F and L, the passive memory "
                            + "matrices with injections B1 and B2 have the same characteristic "
                            + "polynomial. Their scalar spectral roots therefore agree.")),
                    Paragraph(Text(
                        "The result does not say that the matrices, their off-diagonal memory "
                            + "entries, or their products are equal. It isolates the lack of "
                            + "spectral backreaction for this triangular lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-order-witness-is-noncommuting"),
                DeclarationHandle.Create(Prefix + "passive_memory_order_witness"),
                H("A concrete pair of passive memory matrices does not commute"),
                StatementSource.FromAuthor(PassiveMemoryOrderWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two matrices fixed by the displayed premises are precisely the "
                            + "passive lifts with parameters (2, 1, 2) and (2, 2, 3). Their "
                            + "products differ, giving a concrete order-sensitive witness.")),
                    Paragraph(Text(
                        "This establishes existence of noncommuting passive memory steps, not "
                            + "noncommutativity for every parameter choice. Together with the "
                            + "invariance results, it separates stored order from scalar "
                            + "spectral change in this example."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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

    private static Formula Named(Formula name) =>
        Seq(Operatorname, Grp(name));

    private static Formula Subscript(Formula name, Formula index) =>
        Seq(name, Underscore, Grp(index));

    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula PassiveMemoryMatrix(
        Formula update,
        Formula injection,
        Formula readout) =>
        Apply(Named(F.Id("passiveMemoryMatrix")), update, injection, readout);

    private static Formula MemoryHolonomy(
        Formula update,
        Formula injectionScale,
        Formula firstReadout,
        Formula secondReadout) =>
        Apply(
            Named(F.Id("memoryHolonomy")),
            update,
            injectionScale,
            firstReadout,
            secondReadout);

    private static Formula ComplexForAll(
        IReadOnlyList<Formula> variables,
        Formula body)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var index = 0; index < variables.Count; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(variables[index]);
        }

        items.Add(Colon);
        items.Add(Sp);
        items.Add(Complex());
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
        items.Add(body);
        items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula MemoryHolonomyFormula()
    {
        Formula update = F.Id("F");
        Formula injectionScale = F.Id("v");
        Formula firstReadout = Subscript(F.Id("L"), F.Id("p"));
        Formula secondReadout = Subscript(F.Id("L"), F.Id("q"));
        Formula upperRight = Seq(
            Open, secondReadout, Sp, Minus, Sp, firstReadout, Close,
            Open, update, Sp, Minus, Sp, D(1), Close,
            injectionScale);
        Formula defect = Seq(
            Begin, Grp(F.Id("pmatrix")),
            D(0), Amp, upperRight, RowBreak,
            D(0), Amp, D(0),
            End, Grp(F.Id("pmatrix")));

        return ComplexForAll(
            [update, injectionScale, firstReadout, secondReadout],
            Seq(
                MemoryHolonomy(update, injectionScale, firstReadout, secondReadout),
                Sp, Eq, Sp, defect));
    }

    private static Formula MemoryHolonomyTraceZeroFormula() =>
        HolonomyScalarInvariantFormula(Named(F.Id("tr")));

    private static Formula MemoryHolonomyDetZeroFormula() =>
        HolonomyScalarInvariantFormula(Named(F.Id("det")));

    private static Formula HolonomyScalarInvariantFormula(Formula invariant)
    {
        Formula update = F.Id("F");
        Formula injectionScale = F.Id("v");
        Formula firstReadout = Subscript(F.Id("L"), F.Id("p"));
        Formula secondReadout = Subscript(F.Id("L"), F.Id("q"));
        Formula holonomy = MemoryHolonomy(
            update,
            injectionScale,
            firstReadout,
            secondReadout);

        return ComplexForAll(
            [update, injectionScale, firstReadout, secondReadout],
            Seq(Apply(invariant, holonomy), Sp, Eq, Sp, D(0)));
    }

    private static Formula PassiveMemoryTraceInvariantFormula() =>
        PassiveMemoryInvariantFormula(Named(F.Id("tr")));

    private static Formula PassiveMemoryDetInvariantFormula() =>
        PassiveMemoryInvariantFormula(Named(F.Id("det")));

    private static Formula PassiveMemoryCharpolyInvariantFormula() =>
        PassiveMemoryInvariantFormula(Named(F.Id("charpoly")));

    private static Formula PassiveMemoryInvariantFormula(Formula invariant)
    {
        Formula update = F.Id("F");
        Formula readout = F.Id("L");
        Formula firstInjection = Subscript(F.Id("B"), D(1));
        Formula secondInjection = Subscript(F.Id("B"), D(2));
        Formula firstMatrix = PassiveMemoryMatrix(update, firstInjection, readout);
        Formula secondMatrix = PassiveMemoryMatrix(update, secondInjection, readout);

        return ComplexForAll(
            [update, readout, firstInjection, secondInjection],
            Seq(
                Apply(invariant, firstMatrix), Sp, Eq, Sp,
                Apply(invariant, secondMatrix)));
    }

    private static Formula PassiveMemoryOrderWitnessFormula()
    {
        Formula first = F.Id("M");
        Formula second = F.Id("N");
        Formula memoryMatrixType = Named(F.Id("MemoryMatrix"));
        Formula firstValue = PassiveMemoryMatrix(D(2), D(1), D(2));
        Formula secondValue = PassiveMemoryMatrix(D(2), D(2), D(3));

        return Disp(Seq(
            Forall, Sp, first, Comma, Sp, second,
            Colon, Sp, memoryMatrixType, Comma, RowBreak, Grp(),
            Open,
            first, Sp, Eq, Sp, firstValue,
            Sp, Land, Sp,
            second, Sp, Eq, Sp, secondValue,
            Close,
            Sp, Rightarrow, RowBreak, Grp(),
            first, Thin, second, Sp, Neq, Sp, second, Thin, first, Dot));
    }
}
