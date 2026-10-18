using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualFiniteHeadFaithfulnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness.";

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
        Formula c = F.Id("c"), S = F.Id("S"), v = F.Id("v");
        Formula M = F.Id("M"), m = F.Id("m"), n = F.Id("n");
        Formula exteriorNullity = Call("Forall", Call("Typed", m, Call("Int")),
            Seq(Call("Less", Call("NatCastReal", M), Call("abs", Call("IntCastReal", m))),
                Rightarrow, Seq(Call("couplingColumn", c, S, v, m), Eq, D(0))));
        Formula coefficientNullity = Call("Forall", Call("Typed", n, Call("Int")),
            Seq(Call("Member", n, S), Rightarrow, Seq(Call("apply", v, n), Eq, D(0))));
        Formula authorStatement = Call("Forall", Call("Typed", c, Call("Nat")),
            Seq(Call("LessEqual", D(2), c), Rightarrow,
                Call("Forall", Call("Typed", S, Call("Finset", Call("Int"))),
                    Call("Forall", Call("Typed", v, Call("Function", Call("Int"), Call("Complex"))),
                        Call("Forall", Call("Typed", M, Call("Nat")),
                            Seq(exteriorNullity, Rightarrow, coefficientNullity))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "SOURCE_ONLY_UNCOMPILED: author statement for qualitative actual finite-head faithfulness; all acceptance checks remain unperformed.",
            H("Actual Finite Head Faithfulness"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("actual-finite-head-faithful"),
                    DeclarationHandle.Create(Owner + "actual_finite_head_faithful"),
                    H("Exterior nullity determines every finite head coefficient"),
                    StatementSource.FromAuthor(Disp(authorStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("SOURCE_ONLY_UNCOMPILED. For every natural c with 2 <= c, every finite set S of integers, every function v from integers to complex numbers, and every natural M, if for every integer m the inequality (M : Real) < abs((m : Real)) implies couplingColumn(c,S,v,m)=0, then for every integer n, membership n in S implies v(n)=0. This is the full quantified author statement of the exact owner actual_finite_head_faithful; c is implicit in Lean, and hc and hnull are the displayed hypothesis proofs.")),
                        Paragraph(Text("The cutoff M may be zero, S may be empty or contain zero, and v has arbitrary complex values on all integers. Both positive and negative exterior modes are required by abs(m)>M. No head-radius bound, positive moment, q>0, nonempty-head, real-coefficient or weighted-null hypothesis is added. Radius bounds and all analytic cutoffs used in the source proof are constructed internally.")),
                        Paragraph(Text("The actual couplingColumn(c,S,v,m) is the finite sum over n in S of the complex cast of (arithmeticBoundarySymbol(c,n)-arithmeticBoundarySymbol(c,m))/(pi*((m : Real)-(n : Real))), multiplied by v(n). Division is totalized exactly as in the source, including m=n. This retains the actual arithmetic symbol and is not a column made from a freely chosen substitute symbol.")),
                        Paragraph(Text("For the symbol at an integer k, write L=log(c), w=2*pi*k/L and a(j)=2*j+1/2. The pinned definition is arithmeticBoundarySymbol(c,k)=-2*w*(cosh(L/2)-1)/(w^2+1/4)-sum over natural j of w*(1-exp(-a(j)*L))/(a(j)^2+w^2)-sum over j in range(c) of (vonMangoldt(j)/sqrt(j))*sin(w*log(j)). These are the pole, infinite Gamma and finite prime parts, all retained; the lower-chain source candidate supplies the Gamma convergence argument.")),
                        Paragraph(Text("The pinned owner's private coupling_column_recurrence states C(n*v)(m)=m*C(v)(m)-(alpha-symbol(m)*beta)/pi, where alpha=sum over n in S of symbol(n)*v(n), beta=sum over n in S of v(n), symbol=arithmeticBoundarySymbol(c) and C(v)=couplingColumn(c,S,v). The essential factor 1/pi is retained. The totalized diagonal is covered by the summand recurrence.")),
                        Paragraph(Text("The private exterior_null_moments argument consumes ActualFullSymbolTail.paired_coupling_column_tail_lower for the actual columns at both signs. If q=norm(alpha)^2+smoothFloor(c)^2*norm(beta)^2 were positive, an internally chosen cutoff beyond M would give a positive lower bound for a tail that exterior nullity makes zero. Hence q=0, and positivity of smoothFloor(c) for c>=2 forces both alpha=0 and beta=0. Positivity of q is a contradiction case inside the proof, not a theorem premise.")),
                        Paragraph(Text("The recurrence propagates exterior nullity from v(n) to n*v(n); induction propagates it to every node power n^k*v(n). Applying the same moment argument at each power gives all finite node moments zero. The owner then consumes the existing FiniteVandermondeTomography.finite_moment_readout_injective with injective complex casts of the finite integer nodes, so every coefficient on S vanishes, including the empty-head case.")),
                        Paragraph(Text("This is qualitative finite-head faithfulness for actual arithmetic divided-difference columns. It does not establish signed Weil positivity, Robin5040, RH, a quantitative inverse bound, or identification with a physical or canonical Weil operator. The owner and the actual lower-chain dependencies are saved UNCOMPILED source candidates.")),
                        Paragraph(Text("Only source bytes, textual structure and balanced delimiters are checked here. Lean elaboration and real kernel checking, axiom and proof-trust inspection, Reg bridge and whole-family obligations, support enrollment and universes, raw Expr source-selector reconstruction and exact occurrence binding, Scribe compilation and AST/schema/owner checks, rendering and provenance assessment, and every required CI or official acceptance check remain unperformed. Every sourceSelection Expr path in the companion Reg source remains unverified pending actual compilation and inspection."))),
                    DescribeRole.Theorem))));
    }
}
