using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals;

internal sealed class SixStateResidualSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same normalized six-state process has identical stopping archives, distinct permanent residuals, and no almost-sure label update.",
        H("Six-state separation of archives and joint residuals"), Blocks(
            Paragraph(Text("The states s,t,u,v,w,z are Fin(6) indices 0,1,2,3,4,5, and labels 0,1 are false,true. The complete nonzero joint kernel is: s to (0,u) and (0,v), each one half; t to (0,w), mass one; u to (0,z), mass one; v to (1,z), mass one; w to (0,z) and (1,z), each one half; z to (0,z), mass one. Every omitted entry is zero. The rows are nonnegative and normalized. The ordinary absorbing state z can continue forever. All current observations are constant, the unique action is everywhere legal, and there is no failure or extra control.")),
            Paragraph(Text("The original recursive residual is used throughout. firstClass has fibers {s,t,u,z}, {v}, {w}, and equality of firstClass is exactly residual(K,1). stableClass has fibers {s}, {t}, {u,z}, {v}, {w}, and equality of stableClass is exactly residual(K,2). The six signatures using the first-stage classes are: s gives half (0,Czero) plus half (0,Cone); t gives (0,Chalf); u and z give (0,Czero); v gives (1,Czero); w gives half (0,Czero) plus half (1,Czero). Hence s and t agree at the first stage and differ at the second. The only nonsingleton second-stage fiber is {u,z}; both rows send mass one to (0,{u,z}). The next refinement equals the second, and induction gives residual(K,n+2)=residual(K,2) for every n. Its intersection over all horizons is exactly stableClass equality.")),
            Paragraph(Text("For z, an all-zero word has mass one and every other word mass zero, by induction on word length. From s and t the empty word and one-letter word 0 have mass one; the one-letter word 1 has mass zero. A word of length at least two has mass one half exactly when its first letter is 0 and every letter after its second is 0. Thus 00 and 01 each have mass one half, and each may be followed only by zeroes. This computes the same all-depth profile from the same kernel at both initial states. The operational characterization gives equality of every allowed stopping law at every finite horizon, although the second and limiting residuals separate s and t.")),
            Paragraph(Text("representative selects s,t,u,v,w for the five stableClass values. quotientRow(q,(y,d)) sums the original row from representative(q) over successors with stableClass d. The proof checks that every original representative x gives exactly quotientRow(stableClass(x),(y,d)); the only distinct representatives of one fiber are u,z. Summing over y and d gives one, and all entries are nonnegative. StochasticQuotient includes both this normalized joint kernel and the exact identification of stableClass fibers with the original limiting residual. This is a stochastic quotient of the same process, not a separately selected model.")),
            Paragraph(Text("For any proposed deterministic update, updateFailure(update,x) is the sum of the actual original joint masses of branches whose successor class differs from update(stableClass(x),label). From s the two successful branches (0,u) and (0,v) each have mass one half and distinct successor classes. One predicted class cannot equal both; consequently updateFailure(update,s) is at least one half. In particular it cannot be zero, which rules out the update even almost surely. Zero-mass branches are retained in the sum and contribute zero.")),
            Paragraph(Text("claim is the disjunction of two assertions about this one process. The first says that for every pair of states, equality of every finite stopping experiment at every horizon entails equality of the recursive residuals at every horizon. The second says that StochasticQuotient entails existence of a deterministic update with updateFailure zero at every state. Refuting this disjunction refutes each assertion separately: the first uses the all-depth stopping premise at s,t and their actual second-stage separation; the second uses the actual normalized stochastic quotient and the positive update-failure bound.")),
            Describe.Lean(DescribeId.Create("six-state-counterkernel-facts"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.counterkernel_facts"),
                H("Complete same-kernel correction"), StatementSource.FromAuthor(Disp(Facts())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The conjunction gives both complete finite partitions, the permanent plateau and its limiting partition, the actual all-depth word profile and stopping equality, the first-stage agreement and second-stage and limiting separation, the normalized stochastic quotient, and the positive update-failure bound. Every occurrence of kernel denotes the single joint kernel specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-state-residual-separation"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.result"),
                H("Both withdrawn implications fail on the same kernel"),
                StatementSource.FromAuthor(Disp(F.Seq(Neg, Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The two cases of the disjunction are contradicted independently. The archive comparison uses the all-depth common word profile and the exact stopping theorem. The quotient comparison uses its representative independence and normalization before the update obstruction. Thus the random successor-class distribution is well defined, while the current class and observed label do not determine the realized successor class."))), DescribeRole.Theorem),
            Paragraph(Text("The valid implication from recursive residuals to finite archive laws remains. Equality of actual archive laws does not in general identify the recursive quotient or its claimed minimality, and it does not justify merging states in that quotient. No general stochastic factorization or decoder repair is asserted. A common decoder still pushes equal archive laws to equal response laws; identifying those responses with a semantic residual requires a separate characterization. Recursive sufficient-boundary claims must also preserve current observations. The example specifies no semantic event kernel, semantic residual or decoder, so it does not settle theorems under additional such hypotheses. Permission-delay, graft and coordinate-recovery claims retain their own menu, readout, successor and inverse-map conditions. None is proved or refuted here by association, and no physical or empirical consequence follows.")))));

    private static Formula Facts()
    {
        Formula k = F.Id("kernel"), n = F.Id("n"), x = F.Id("x"), xp = F.Id("xp"), w = F.Id("w");
        Formula six = Call("Fin", D(6)), five = Call("Fin", D(5)), nat = F.Id("Nat");
        Formula a = All("x", six, All("xp", six, Seq(Call("residual", k, D(1), x, xp), Leftrightarrow,
            Call("firstClass", x), Eq, Call("firstClass", xp))));
        Formula b = All("x", six, All("xp", six, Seq(Call("residual", k, D(2), x, xp), Leftrightarrow,
            Call("stableClass", x), Eq, Call("stableClass", xp))));
        Formula c = All("n", nat, Seq(Call("residual", k, Seq(n, Plus, D(2))), Eq, Call("residual", k, D(2))));
        Formula d = All("x", six, All("xp", six, Seq(Open,
            All("n", nat, Call("residual", k, n, x, xp)), Close, Leftrightarrow,
            Call("stableClass", x), Eq, Call("stableClass", xp))));
        Formula e = All("w", Call("List", F.Id("Bool")), Seq(Call("wordProb", k, D(0), w), Eq,
            Call("profile", w), Land, Sp, Call("wordProb", k, D(1), w), Eq, Call("profile", w)));
        Formula f = All("n", nat, Call("StoppingEq", k, n, D(0), D(1)));
        Formula g = Call("residual", k, D(1), D(0), D(1));
        Formula h = Seq(Neg, Sp, Call("residual", k, D(2), D(0), D(1)));
        Formula i = Seq(Neg, Sp, Open, All("n", nat, Call("residual", k, n, D(0), D(1))), Close);
        Formula j = F.Id("StochasticQuotient");
        Formula l = All("update", Seq(five, Rightarrow, Sp, F.Id("Bool"), Rightarrow, Sp, five),
            Seq(Fraction(D(1), D(2)), Leq, Call("updateFailure", F.Id("update"), D(0))));
        return And(a,b,c,d,e,f,g,h,i,j,l);
    }
    private static Formula And(params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 4 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            var z = 4 * i;
            parts[z] = Open; parts[z+1] = xs[i]; parts[z+2] = Close;
            if (i < xs.Length - 1) parts[z+3] = F.Seq(Land, Sp);
        }
        return Seq(parts);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++) { parts[2*i] = xs[i]; if (i > 0) parts[2*i-1] = Comma; }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
