using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.KolmogorovSinai;

internal sealed class FairEquilibriumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/morgenstern2026ks");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FairEquilibrium", H("Fair Equilibrium"), Blocks(
            Paragraph(Text("The coordinate partition generates the Borel sigma-algebra. The supplier generator theorem reduces the genuine KS supremum to its entropy rate. The entropy bound and the attained Bernoulli value are log 2. Equality forces the maximum entropy value for every finite-word distribution. Existing EntropyEquality gives uniform word masses; the cylinder pi-system determines the law. Measurable conjugacy transports both the invariant measure and the full KS supremum to positive source indices and symbols 1,2. Thus the same source-space fair law is the unique KS maximizer. No target existence or zero-deficit bridge is assumed.")),
            Describe.Lean(DescribeId.Create("fair"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair"),
                H("fair"), StatementSource.FromAuthor(CompletedPresentation8()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fair-invariant"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_invariant"),
                H("fair invariant"), StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ks-le"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.ks_le"),
                H("ks le"), StatementSource.FromAuthor(Presentation1()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fair-ks"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_ks"),
                H("fair ks"), StatementSource.FromAuthor(Presentation2()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("max-unique"),
                DeclarationHandle.Create("D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.max_unique"),
                H("max unique"), StatementSource.FromAuthor(Presentation3()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem))));

    private static Formula Presentation0() => Disp(Seq(F.Id("MeasureTheory"), Dot, F.Id("MeasurePreserving"), Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"),
            Dot, F.Id("LopesOliveiraFullTail"), Dot, F.Id("shift"), Sp, F.Id("D5"), Dot, F.Id("S3"), Dot,
            F.Id("Entropy"), Dot, F.Id("SourceEquilibrium"), Dot, F.Id("fair"), Sp, F.Id("D5"), Dot, F.Id("S3"),
            Dot, F.Id("Entropy"), Dot, F.Id("SourceEquilibrium"), Dot, F.Id("fair")));
    private static Formula Presentation1() => Disp(Seq(Forall, Sp, Open, F.Id("rho"), Sp, Colon, Sp, F.Id("MeasureTheory"), Dot,
            F.Id("Measure"), Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("LopesOliveiraFullTail"),
            Dot, F.Id("Omega"), Close, Sp, OpenBracket, F.Id("MeasureTheory"), Dot, F.Id("IsProbabilityMeasure"), Sp,
            F.Id("rho"), CloseBracket, Sp, Open, F.Id("hT"), Sp, Colon, Sp, F.Id("MeasureTheory"),
            Dot, F.Id("MeasurePreserving"), Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot,
            F.Id("LopesOliveiraFullTail"), Dot, F.Id("shift"), Sp, F.Id("rho"), Sp, F.Id("rho"), Close, Comma,
            Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot,
            F.Id("ksEntropy"), Sp, F.Id("hT"), Sp, Le, Sp, Open, F.Id("Real"), Dot,
            F.Id("log"), Sp, new Formula.Number(2), Close));
    private static Formula Presentation2() => Disp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot, F.Id("ksEntropy"),
            Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("SourceEquilibrium"), Dot,
            Grp(F.Id("fair"), Seq(Underscore, Grp(F.Id("invariant")))), Sp, Eq, Sp, Open, F.Id("Real"), Dot, F.Id("log"), Sp,
            new Formula.Number(2), Close));
    private static Formula Presentation3() => Disp(Seq(Forall, Sp, Open, F.Id("rho"), Sp, Colon, Sp, F.Id("MeasureTheory"), Dot,
            F.Id("Measure"), Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("LopesOliveiraFullTail"),
            Dot, F.Id("Omega"), Close, Sp, OpenBracket, F.Id("MeasureTheory"), Dot, F.Id("IsProbabilityMeasure"), Sp,
            F.Id("rho"), CloseBracket, Sp, Open, F.Id("hT"), Sp, Colon, Sp, F.Id("MeasureTheory"),
            Dot, F.Id("MeasurePreserving"), Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot,
            F.Id("LopesOliveiraFullTail"), Dot, F.Id("shift"), Sp, F.Id("rho"), Sp, F.Id("rho"), Close, Comma,
            Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("KolmogorovSinai"), Dot,
            F.Id("ksEntropy"), Sp, F.Id("hT"), Sp, Eq, Sp, Open, F.Id("Real"), Dot,
            F.Id("log"), Sp, new Formula.Number(2), Close, Sp, To, Sp, F.Id("rho"), Sp,
            Eq, Sp, F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("SourceEquilibrium"),
            Dot, F.Id("fair")));
    private static Formula CompletedPresentation8() => Disp(Seq(F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("SourceEquilibrium"), Dot, F.Id("fair"),
            Sp, Eq, Sp, F.Id("MeasureTheory"), Dot, F.Id("Measure"), Dot, F.Id("map"), Sp,
            F.Id("D5"), Dot, F.Id("S3"), Dot, F.Id("Entropy"), Dot, F.Id("LopesOliveiraFullTail"), Dot, F.Id("coordinateEquiv"),
            Sp, Open, F.Id("MeasureTheory"), Dot, F.Id("Measure"), Dot, F.Id("infinitePi"), Sp, Open,
            LambdaLower, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto,
            Sp, Open, new Formula.Number(2), Sp, Colon, Sp, F.Id("ENNReal"), Grp(Close, Seq(Caret, Grp(Minus, D(1)))), Sp,
            Cdot, Sp, F.Id("MeasureTheory"), Dot, F.Id("Measure"), Dot, F.Id("dirac"), Sp, F.Id("false"),
            Sp, Plus, Sp, Open, new Formula.Number(2), Sp, Colon, Sp, F.Id("ENNReal"),
            Grp(Close, Seq(Caret, Grp(Minus, D(1)))), Sp, Cdot, Sp, F.Id("MeasureTheory"), Dot, F.Id("Measure"), Dot, F.Id("dirac"),
            Sp, F.Id("true"), Close, Close));
}
