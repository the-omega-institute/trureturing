using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualFullSymbolTailDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), m = F.Id("m"), n = F.Id("n"), N = F.Id("N");
        return DocumentDefinition.Create(ScribeNode.Create(
            "SOURCE_ONLY_UNCOMPILED: faithful author statements; no validated provenance claim.",
            H("Actual Full Arithmetic Symbol Tail"),
            Blocks(
                Paragraph(Text("All new Lean bodies, imported T2/T3 attempts, this Scribe DSL, and Reg registrations await actual caller-owned verification.")),
                Describe.Lean(
                    DescribeId.Create("prime-first-moment"),
                    DeclarationHandle.Create(Owner + "primeFirstMoment"),
                    H("The actual finite first-moment constant"),
                    StatementSource.FromAuthor(Disp(Seq(Call("K", c), Eq, Call("PhaseDenominatorSum", c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("K(c)=sum_{q in Ico(2,c)} 2*abs(primeWeight(q))/norm(1-primePhase(c,q)). Every integer in the range is present, hence all prime powers; no phase-spacing premise is supplied. For c=2 this is the empty sum."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("full-symbol-tail-budget"),
                    DeclarationHandle.Create(Owner + "fullSymbolTailBudget"),
                    H("The refined full-symbol budget"),
                    StatementSource.FromAuthor(Disp(Seq(Call("B", c, N), Eq, Call("T3tailBudget", c, N), Plus, Call("div", Call("square", Call("E", c, N)), N), Plus, Call("div", Seq(D(2), Sp, Call("K", c), Sp, Call("E", c, Seq(N, Plus, D(1)))), Call("square", Seq(N, Plus, D(1))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("B(c,N)=PrimeSymbolResonance.tailBudget(c,N)+E(c,N)^2/N+2*K(c)*E(c,N+1)/(N+1)^2. Here the owner's sharpened finite envelope is E(c,m)=min(2+U(c)/m,pi/4+(U(c)+3/(4*a(c)))/m), with a=2*pi/log(c) and U=2*(cosh(log(c)/2)-1)/a. The full-tail Lean source and its public signatures are unchanged. T3 is the unchanged, uncompiled source attempt. The factor two comes from the actual A=H-S square. For fixed c>=2 the candidate envelope tends to pi/4; the smooth-square contribution then has leading coefficient pi^2/16 in 1/N, and its contribution after the existing paired factor 2/pi^2 has coefficient 1/8 multiplying norm(beta)^2/N. These limit interpretations still require real verification, are not asserted as new Lean limit theorems, and do not remove the prime tail, either moment, or the mixed term. This finite tail improvement proves no RH, Robin inequality, strict positivity, full column remainder or physical operator identification."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("prime-first-moment-block"),
                    DeclarationHandle.Create(Owner + "prime_first_moment_block"),
                    H("Every actual prime first-moment block"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Call("abs", Call("PrimeBlock", c, F.Id("M"), F.Id("k"))), Leq, Call("K", c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For c>=2, any integer start M and any natural length k, abs(sum_{j<k} S(c,M+j))<=K(c), including k=0. The complex imaginary-part representation and geometric_block_norm are the existing T2 statements. Its actual phase lies strictly between angles zero and 2*pi, proving phase!=1 for each included q."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("signed-mixed-partial"),
                    DeclarationHandle.Create(Owner + "signed_mixed_partial"),
                    H("Signed finite mixed tail with the refined minimum"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Call("abs", Call("FiniteMixed", c, N, F.Id("k"))), Leq, Call("div", Seq(Call("K", c), Sp, Call("E", c, Seq(N, Plus, D(1)))), Call("square", Seq(N, Plus, D(1))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For c>=2, any natural N and any natural k, FiniteMixed is sum_{j<k} S_m*(A_m+S_m)/m^2, m=N+j+1. The proof applies the existing signed finite_abel_majorant twice at D=0,C=K, to x=S and x=-S, with the actual nonnegative antitone weight. The complete finite boundary term remains accounted for; no boundary limit is assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("signed-mixed-tail"),
                    DeclarationHandle.Create(Owner + "signed_mixed_tail"),
                    H("Absolute convergence followed by actual mixed tsum passage"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", N), Rightarrow, Call("AbsolutelySummable", Call("MixedSequence", c, N)), Land, Call("abs", Call("MixedTsum", c, N)), Leq, Call("div", Seq(Call("K", c), Sp, Call("E", c, Seq(N, Plus, D(1)))), Call("square", Seq(N, Plus, D(1))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For c>=2 and N>0, sum_j abs(S_m*(A_m+S_m)/m^2) converges and abs(tsum_j S_m*(A_m+S_m)/m^2)<=K(c)*E(c,N+1)/(N+1)^2, m=N+j+1. Absolute summability uses the finite sum of absolute prime weights times E(c,N) and the existing inverse-square summability. Only then does HasSum.tendsto_sum_nat pass the finite signed bound to the actual tsum."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("full-symbol-square-tail"),
                    DeclarationHandle.Create(Owner + "full_symbol_square_tail"),
                    H("The complete actual symbol square tail"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", N), Rightarrow, Call("Summable", Call("FullEnergySequence", c, N, F.Id("beta"))), Land, Call("FullEnergyTsum", c, N, F.Id("beta")), Leq, Call("normSq", F.Id("beta")), Sp, Call("B", c, N)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For c>=2, N>0 and arbitrary complex beta, the nonnegative sequence norm(beta*A(c,N+j+1)/(N+j+1))^2 is summable and its actual tsum is <=norm(beta)^2*B(c,N). A is exactly arithmeticBoundarySymbol. The proof sums A^2=S^2+H^2-2*S*H using established convergence of all three terms, and pays twice the absolute signed mixed estimate. There is no reality, vanishing, positivity or spacing hypothesis."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("paired-first-jet-tail"),
                    DeclarationHandle.Create(Owner + "paired_first_jet_tail"),
                    H("Both exterior signs with both retained head moments"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", N), Rightarrow, Call("Summable", Call("PairedJetSequence", c, N, F.Id("S"), F.Id("v"))), Land, Call("PairedJetTsum", c, N, F.Id("S"), F.Id("v")), Leq, Call("div", D(2), Call("square", F.Id("pi"))), Sp, Grp(Call("div", Call("normSq", F.Id("alpha")), N), Plus, Call("normSq", F.Id("beta")), Sp, Call("B", c, N))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For any finite integer S and complex v, alpha=sum_{n in S} A(c,n)*v(n) and beta=sum_{n in S} v(n). The summed sequence is norm(couplingFirstJet(m))^2+norm(couplingFirstJet(-m))^2, m=N+j+1. It is summable and bounded by (2/pi^2)*(norm(alpha)^2/N+norm(beta)^2*B(c,N)). Native arithmetic_boundary_symbol_neg is reused and the private complex parallelogram calculation is consumed here. This paired enumeration includes both exterior signs. A literal tsum over an integer subtype is not asserted. The physical operator bridge and column remainder remain separate."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("paired-jet-budget"),
                    DeclarationHandle.Create(Owner + "pairedJetBudget"),
                    H("Both complex first-jet moments retained"),
                    StatementSource.FromAuthor(Disp(Seq(Call("J", c, N, F.Id("S"), F.Id("v")), Eq, Call("mul", Call("div", D(2), Call("square", F.Id("pi"))), Call("add", Call("div", Call("normSq", F.Id("alpha")), N), Call("mul", Call("normSq", F.Id("beta")), Call("fullSymbolTailBudget", c, N))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. J=(2/pi^2)*(norm(alpha)^2/M+norm(beta)^2*fullSymbolTailBudget(c,M)), alpha=sum A_c(n)*v(n), beta=sum v(n). This is exactly the existing paired_first_jet_tail budget, including every actual prime power and the complete pole, refined Gamma and mixed terms."))),
                    DescribeRole.Definition),
                // SOURCE_ONLY_UNCOMPILED. Insert this one expression in the existing Full
                // document's Blocks, immediately before its last paired-column upper Describe.
                // Reuse input08's Owner, Call, c and N; retain its imports/namespace/class.
                Describe.Lean(
                    DescribeId.Create("paired-coupling-column-tail-lower"),
                    DeclarationHandle.Create(Owner + "paired_coupling_column_tail_lower"),
                    H("The actual paired column has a quantitative lower tail"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Forall", c, N, F.Id("S"), F.Id("v"), F.Id("A")), Sp,
                        Call("let", F.Id("alpha"),
                            Call("sum", F.Id("n"), F.Id("S"),
                                Call("mul", Call("complexCast", Call("arithmeticBoundarySymbol", c, F.Id("n"))),
                                    Call("v", F.Id("n"))))), Sp,
                        Call("let", F.Id("beta"), Call("sum", F.Id("n"), F.Id("S"), Call("v", F.Id("n")))), Sp,
                        Call("let", F.Id("q"), Call("add", Call("square", Call("norm", F.Id("alpha"))),
                            Call("mul", Call("square", Call("smoothFloor", c)), Call("square", Call("norm", F.Id("beta")))))), Sp,
                        Call("let", F.Id("U"), Call("div",
                            Call("mul", D(2), Call("sub", Call("cosh", Call("div", Call("logLength", c), D(2))), D(1))),
                            Call("div", Call("mul", D(2), F.Id("pi")), Call("logLength", c)))), Sp,
                        Call("let", F.Id("D0"), Call("mul", D(2), Call("primeFirstMoment", c), Call("add", D(2), F.Id("U")))), Sp,
                        Call("And", Call("AtLeastTwo", c), Call("PositiveNatural", N),
                            Call("FiniteIntegerHead", F.Id("S")), Call("ComplexCoefficients", F.Id("v")),
                            Call("Nonnegative", F.Id("A")), Call("HeadWithin", F.Id("S"), F.Id("A")),
                            Call("LessEqual", D(1), Call("frequency", c, Call("add", N, D(1)))),
                            Call("LessEqual", Call("mul", D(2), F.Id("A")), Call("add", N, D(1))),
                            Call("Positive", F.Id("q")),
                            Call("LessEqual", Call("div", Call("mul", D(2), Call("square", Call("norm", F.Id("beta"))), F.Id("D0")), F.Id("q")), Call("add", N, D(1))),
                            Call("LessEqual", Call("div", Call("mul", D(2, 5, 6), Call("square", Call("arithmeticBoundaryBudget", c)),
                                Call("square", Call("weightedHeadMass", F.Id("S"), F.Id("v")))), Call("mul", D(3), F.Id("q"))), Call("square", N))),
                        Rightarrow,
                        Call("And",
                            Call("Summable", Call("lambda", F.Id("j"),
                                Call("add",
                                    Call("square", Call("norm", Call("couplingColumn", c, F.Id("S"), F.Id("v"), Call("add", N, F.Id("j"), D(1))))),
                                    Call("square", Call("norm", Call("couplingColumn", c, F.Id("S"), F.Id("v"), Call("neg", Call("add", N, F.Id("j"), D(1))))))))),
                            Call("LessEqual", Call("div", F.Id("q"), Call("mul", D(4), Call("square", F.Id("pi")), Call("add", N, D(1)))),
                                Call("tsum", F.Id("j"),
                                    Call("add",
                                        Call("square", Call("norm", Call("couplingColumn", c, F.Id("S"), F.Id("v"), Call("add", N, F.Id("j"), D(1))))),
                                        Call("square", Call("norm", Call("couplingColumn", c, F.Id("S"), F.Id("v"), Call("neg", Call("add", N, F.Id("j"), D(1))))))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("SOURCE_ONLY_UNCOMPILED. For every natural c>=2 and M>0, every finite S subset Z, every v:Z->C, and real A>=0 with abs(n)<=A on S, use the actual moments alpha=sum_{n in S}(arithmeticBoundarySymbol(c,n):C)*v(n) and beta=sum_{n in S}v(n). Put delta=smoothFloor(c)=(1-exp(-logLength(c)/2))/10, q=norm(alpha)^2+delta^2*norm(beta)^2, U=2*(cosh(logLength(c)/2)-1)/(2*pi/logLength(c)), and D0=2*primeFirstMoment(c)*(2+U). The displayed N denotes this same M; all mode arguments are integer casts.")),
                        Paragraph(Text("The complete cutoffs are frequency(c,M+1)>=1, M+1>=2*A, q>0, M+1>=2*norm(beta)^2*D0/q, and M^2>=256*arithmeticBoundaryBudget(c)^2*weightedHeadMass(S,v)^2/(3*q). Under all these conditions, the exact sequence norm(couplingColumn(c,S,v,M+j+1))^2+norm(couplingColumn(c,S,v,-(M+j+1)))^2 is summable and q/(4*pi^2*(M+1)) is at most its single paired tsum.")),
                        Paragraph(Text("The proof consumes the actual all-c Gamma finite-block floor in Jet, the full-real floor/coarse lower bound, the exact two-moment jet identity, the positive-real inverse-square lower comparison, and the actual reverse-energy inequality with the migrated remainder budget. The half-gap gives R<=32*B^2*weightedHeadMass^2/(3*pi^2*M^3); the last cutoff gives R<=q/(4*pi^2*(M+1)). No division by beta, B or weightedHeadMass is used.")),
                        Paragraph(Text("This includes c=2 with alpha=0 and beta nonzero, and beta=0 when alpha is nonzero. A nonzero coefficient function need not give q>0. The q=0 case is excluded from this inverse-linear conclusion; the existing upper-tail remainder theorem remains available there. This is a bound for the actual arithmetic column, with no claim of worldwide novelty, signed Weil-form positivity, RH/Robin, or Fourier/physical operator identification. Kernel acceptance, complete source reconstruction and enrollment, Scribe emission, and required checks remain caller-owned and unperformed."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("paired-coupling-column-tail"),
                    DeclarationHandle.Create(Owner + "paired_coupling_column_tail"),
                    H("The full paired actual column with the square-root budget"),
                    StatementSource.FromAuthor(Disp(Seq(Call("And", Call("AtLeastTwo", c), Call("Positive", N), Call("Nonnegative", F.Id("A")), Call("HeadWithin", F.Id("S"), F.Id("A")), Call("Less", F.Id("A"), Call("add", N, D(1)))), Rightarrow, Call("And", Call("Summable", Call("PairedColumnSequence", c, N, F.Id("S"), F.Id("v"))), Call("LessEqual", Call("PairedColumnTsum", c, N, F.Id("S"), F.Id("v")), Call("square", Call("add", Call("sqrt", Call("J", c, N, F.Id("S"), F.Id("v"))), Call("sqrt", Call("R", c, N, F.Id("A"), F.Id("S"), F.Id("v")))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("SOURCE_ONLY_UNCOMPILED. Under precisely c>=2, M>0, A>=0, A<M+1, abs(n)<=A on arbitrary finite S, and arbitrary complex v, the sequence norm(couplingColumn(m))^2+norm(couplingColumn(-m))^2 for m=M+j+1 is summable and its genuine tsum is <=(sqrt(J)+sqrt(R))^2. The proof applies the pinned Real.sum_mul_le_sqrt_mul_sqrt to the finite index set range(k) times Bool, with the actual jet and column-minus-jet, obtains that same uniform partial-sum bound, and passes to the infinite nonnegative sum. No fixed factor-two energy loss is introduced. In the two-moment-annihilating application alpha=beta=0, J=0, so this same bound specializes to R without any new named corollary. All assertions, imported source candidates, AST selections and Scribe DSL remain uncompiled; kernel, axioms, compiled Reg source reconstruction and enrollment, Scribe emission, reports and required CI are pending. Actual operator Fourier identification and RH positivity remain separate. The unrelated FIB five-probability-mode model is not identified with five arbitrary Fourier coefficients. No Pro participation or diverse consensus is claimed; latest proper broker readiness is refresh_token_expired."))),
                    DescribeRole.Theorem))));
    }
}
