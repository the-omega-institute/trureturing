using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class BaezDuarteContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original coefficient decay gives holomorphic Newton continuation, compact uniformity through one, and standard RH.",
        H("Baez-Duarte continuation through the pole"),
        Blocks(
            Paragraph(Text("For every displayed statement, c is the existing real baezDuarte coefficient, cComplex its original complex finite sum, and P the existing normalizedPochhammer polynomial. H is the open half-plane Re(s)>1/2; F(s) is the tsum of term(s)(k)=c(k)P(k,s/2); partial(N,s) is the sum of these terms over range N. Decay(c) means: for every real epsilon>0 there are real C>0 and natural N>=1 such that for every k>=N, |c(k)|<=C*k^(-3/4+epsilon). DecayHalf uses epsilon/2 instead. Compact(K) below means K is compact and K is a subset of H. All s and k are universally quantified in their stated domains. The entire multiplier riemannZetaOne is mathlib riemannZeta₁, and analyticReciprocal(s)=(s-1)/riemannZeta₁(s).")),
            Describe.Lean(
                DescribeId.Create("complex-finite-sum"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_complex_finite_sum"),
                H("Original finite coefficients"),
                StatementSource.FromAuthor(Statement(0)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The cast of the real coefficient equals the original complex binomial sum, using realness of zeta at the positive even integers. No decay hypothesis is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("summable"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_summable"),
                H("Pointwise absolute convergence"),
                StatementSource.FromAuthor(Statement(1)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The existing compact majorant applied to a singleton proves summability of the actual Newton terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_uniform"),
                H("Uniform convergence on every compact subset"),
                StatementSource.FromAuthor(Statement(2)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The range partial sums converge uniformly to their actual tsum on every compact subset of Re(s)>1/2. Empty compacts and all finite prefixes are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("locally-uniform"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_locally_uniform"),
                H("Locally uniform convergence"),
                StatementSource.FromAuthor(Statement(3)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("Compact uniform convergence on the open half-plane supplies locally uniform convergence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holomorphic"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_differentiable"),
                H("Holomorphic Newton sum"),
                StatementSource.FromAuthor(Statement(4)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("Each term is a polynomial in s, and the locally uniform limit is complex differentiable throughout the open half-plane."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_regularized_product"),
                H("Regularized product identity"),
                StatementSource.FromAuthor(Statement(5)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("Analytic uniqueness continues the initial identity from a neighborhood of two to the connected half-plane. The entire multiplier is the public mathlib riemannZeta₁; zero-freeness is proved from the identity and is not a premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_at_one"),
                H("The sum at one is zero"),
                StatementSource.FromAuthor(Statement(6)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The analytic reciprocal has value zero at one. This is not the reciprocal of the totalized raw zeta value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal"),
                H("The analytic reciprocal on the whole half-plane"),
                StatementSource.FromAuthor(Statement(7)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The actual Newton terms have sum (s-1)/riemannZeta₁(s), including at one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-one"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal_off_one"),
                H("Raw reciprocal away from one"),
                StatementSource.FromAuthor(Statement(8)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("Off one, the same series has sum 1/riemannZeta(s). No statement identifies the raw reciprocal with the analytic extension at one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal-uniform"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal_uniform"),
                H("Compact uniformity across the pole"),
                StatementSource.FromAuthor(Statement(9)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The range partial sums converge uniformly to the analytic reciprocal on every compact subset of the half-plane, including compacts that contain or cross one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decay-rh"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_decay_implies_rh"),
                H("Coefficient decay implies standard RH"),
                StatementSource.FromAuthor(Statement(10)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The all-positive-epsilon bound on the actual coefficients excludes zeta zeros in the right half of the critical strip and applies the existing standard RH reduction. The necessity direction is a separate remaining obligation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("epsilon"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_epsilon_half_iff"),
                H("Both epsilon conventions agree"),
                StatementSource.FromAuthor(Statement(11)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("Quantification over every positive epsilon makes the exponents -3/4+epsilon and -3/4+epsilon/2 equivalent. This says nothing about epsilon zero or the boundary line Re(s)=1/2."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement(int index)
    {
        Formula s = FormulaDsl.Id("s"), k = FormulaDsl.Id("k"), c = FormulaDsl.Id("c");
        Formula K = FormulaDsl.Id("K"), F = FormulaDsl.Id("F"), Hset = FormulaDsl.Id("H");
        Formula partial = FormulaDsl.Id("partial"), decay = Call("Decay", c);
        Formula compact = Call("Compact", K), member = Seq(s, InMacro, Sp, Hset);
        Formula reciprocal = new Formula.Fraction(Seq(s, Minus, D(1)), Call("riemannZetaOne", s));
        return Disp(index switch
        {
            0 => Seq(Call("c", k), Eq, Call("cComplex", k)),
            1 => Seq(decay, Rightarrow, Sp, Call("Summable", Call("term", s))),
            2 => Seq(decay, Land, Sp, compact, Rightarrow, Sp, Call("TendstoUniformlyOn", partial, F, Call("atTop"), K)),
            3 => Seq(decay, Rightarrow, Sp, Call("TendstoLocallyUniformlyOn", partial, F, Call("atTop"), Hset)),
            4 => Seq(decay, Rightarrow, Sp, Call("DifferentiableOn", Call("Complex"), F, Hset)),
            5 => Seq(decay, Land, Sp, member, Rightarrow, Sp, Call("riemannZetaOne", s), Sp, Call("F", s), Eq, s, Minus, D(1)),
            6 => Seq(decay, Rightarrow, Sp, Call("HasSum", Call("term", D(1)), D(0))),
            7 => Seq(decay, Land, Sp, member, Rightarrow, Sp, Call("HasSum", Call("term", s), reciprocal)),
            8 => Seq(decay, Land, Sp, member, Land, Sp, s, Neq, Sp, D(1), Rightarrow, Sp, Call("HasSum", Call("term", s), new Formula.Fraction(D(1), Call("riemannZeta", s)))),
            9 => Seq(decay, Land, Sp, compact, Rightarrow, Sp, Call("TendstoUniformlyOn", partial, Call("analyticReciprocal"), Call("atTop"), K)),
            10 => Seq(decay, Rightarrow, Sp, Call("RiemannHypothesis")),
            11 => Seq(decay, Iff, Sp, Call("DecayHalf", c)),
            _ => throw new System.ArgumentOutOfRangeException(nameof(index)),
        });
    }
}
