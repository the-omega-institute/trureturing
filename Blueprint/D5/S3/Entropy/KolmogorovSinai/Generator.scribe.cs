using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.KolmogorovSinai;

internal sealed class GeneratorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/morgenstern2026ks");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator", H("Generator"), Blocks(
            Paragraph(Text("Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.")),
            Describe.Lean(DescribeId.Create("ksentropypartition-le-ksentropyseq-div"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropyPartition_le_ksEntropySeq_div"),
                H("ksEntropyPartition le ksEntropySeq div"), StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ksentropy-eq-ksentropypartition-of-generating"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropy_eq_ksEntropyPartition_of_generating"),
                H("ksEntropy eq ksEntropyPartition of generating"), StatementSource.FromAuthor(Presentation1()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-partition-refinement-entropy"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/Generator.entropy_le_of_partition_refinement"),
                H("Entropy under finite partition refinement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entropy of the coarser partition is bounded by the entropy of its refinement. The common join has the entropy of the refining partition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ks-entropy-increasing-saturations"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropy_le_of_increasing_partition_saturations"),
                H("Entropy bounds from increasing partition saturations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A uniform entropy bound for finite observations bounds the full system entropy when their forward orbit sigma algebras increase to the ambient sigma algebra. The partition-relative conditional entropy of any fixed test partition tends to zero. The comparison uses the finite-window argument of Morgenstern's two-sided generator theorem."))),
                DescribeRole.Theorem))));

    private static Formula Presentation0() => Disp(Seq(Forall, Sp, OpenBrace, Alpha, Sp, Colon, Sp, F.Id("Type"), CloseBrace,
            Sp, OpenBrace, Iota, Sp, Colon, Sp, F.Id("Type"), CloseBrace, Sp,
            OpenBracket, F.Id("MeasurableSpace"), Sp, Alpha, CloseBracket, Sp, OpenBracket, F.Id("Fintype"), Sp,
            Iota, CloseBracket, Sp, OpenBrace, Mu, Sp, Colon, Sp, F.Id("MeasureTheory"),
            Dot, F.Id("Measure"), Sp, Alpha, CloseBrace, Sp, OpenBracket, F.Id("MeasureTheory"), Dot,
            F.Id("IsProbabilityMeasure"), Sp, Mu, CloseBracket, Sp, OpenBrace, Sp, F.Id("T"), Sp, Colon,
            Sp, Alpha, Sp, To, Sp, Alpha, CloseBrace, Sp, Open,
            F.Id("hT"), Sp, Colon, Sp, F.Id("MeasureTheory"), Dot, F.Id("MeasurePreserving"), Sp, F.Id("T"),
            Sp, Mu, Sp, Mu, Close, Sp, Open, F.Id("P"), Sp,
            Colon, Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"),
            Dot, F.Id("MeasurePartition"), Sp, Mu, Sp, Iota, Close, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), CloseBrace, Comma, Sp, new Formula.Number(1),
            Sp, Le, Sp, F.Id("n"), Sp, To, Sp, F.Id("D5"), Dot,
            F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("ksEntropyPartition"), Sp, F.Id("hT"),
            Sp, F.Id("P"), Sp, Le, Sp, F.Id("D5"), Dot, F.Id("S3"), Dot,
            F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("ksEntropySeq"), Sp, F.Id("hT"), Sp, F.Id("P"),
            Sp, F.Id("n"), Sp, Slash, Sp, F.Id("n")));
    private static Formula Presentation1() => Disp(Seq(Forall, Sp, OpenBrace, Alpha, Sp, Colon, Sp, F.Id("Type"), CloseBrace,
            Sp, OpenBracket, F.Id("m"), Alpha, Sp, Colon, Sp, F.Id("MeasurableSpace"), Sp,
            Alpha, CloseBracket, Sp, OpenBracket, F.Id("StandardBorelSpace"), Sp, Alpha, CloseBracket, Sp,
            OpenBrace, Mu, Sp, Colon, Sp, F.Id("MeasureTheory"), Dot, F.Id("Measure"), Sp,
            Alpha, CloseBrace, Sp, OpenBracket, F.Id("MeasureTheory"), Dot, F.Id("IsProbabilityMeasure"), Sp, Mu,
            CloseBracket, Sp, OpenBrace, Sp, F.Id("T"), Sp, Colon, Sp, Alpha, Sp,
            To, Sp, Alpha, CloseBrace, Sp, Open, F.Id("hT"), Sp, Colon,
            Sp, F.Id("MeasureTheory"), Dot, F.Id("MeasurePreserving"), Sp, F.Id("T"), Sp, Mu, Sp,
            Mu, Close, Sp, OpenBrace, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
            CloseBrace, Sp, Open, F.Id("P"), Sp, Colon, Sp, F.Id("D5"), Dot,
            F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("MeasurePartition"), Sp, Mu,
            Sp, Open, F.Id("Fin"), Sp, F.Id("n"), Close, Close, Comma, Sp,
            F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("IsGenerating"),
            Sp, Mu, Sp, F.Id("T"), Sp, F.Id("P"), Sp, To, Sp,
            F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("ksEntropy"),
            Sp, F.Id("hT"), Sp, Eq, Sp, Open, F.Id("D5"), Dot, F.Id("S3"),
            Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("ksEntropyPartition"), Sp, F.Id("hT"), Sp,
            F.Id("P"), Close));
}
