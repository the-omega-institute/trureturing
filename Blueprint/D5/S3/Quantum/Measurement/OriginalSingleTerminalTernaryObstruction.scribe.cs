using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OriginalSingleTerminalTernaryObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original causal leaf law places every joint ternary postprocessing in a common closed score halfspace.",
        H("Original Single-Terminal Ternary Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-original-single-terminal-ternary-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurement/OriginalSingleTerminalTernaryObstruction."
                    + "complete_original_single_terminal_ternary_obstruction"),
                H("Complete records obey the ternary score obstruction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Source retains 0<d<1, sin(2 theta) nonzero, the same installed "
                        + "unitary N with nonzero commutator with the xi projector, and the "
                        + "original V0=U exp(i theta W), V1=V0 W, W=I-2ff*, "
                        + "q=(xi+e)/sqrt(2), E=qq*. The sole installed preparation is the "
                        + "rank-one density of sqrt(d)Uq+i sqrt(1-d)Uf. The rectangular "
                        + "isometry B and Kb B=B Vb/sqrt(2) retain the five-dimensional "
                        + "source correspondence as premises.")),
                    Paragraph(Text(
                        "A CausalTree is a finite complete tree. A control node applies the "
                        + "same N, an instrument node retains both original J outcomes with "
                        + "branch Ad(Vb)/2, and a stop node performs the original two-cell "
                        + "terminal exactly once and stops. Leaves are never identified by "
                        + "their marks: their complete chronological words, action positions, "
                        + "labels, mismatch marks and timeout marks remain distinct. Empty "
                        + "words, no-control trees, no-instrument trees and unequal depths "
                        + "are included. There is no successor operation after the terminal.")),
                    Paragraph(Text(
                        "fixedStoppingTree embeds every finite fixed action string, "
                        + "checkpoint function and past-label stopping table. Continuing "
                        + "uses the same remaining string, while the end is forced. The "
                        + "universal causal tree domain also permits the larger mathematical "
                        + "comparison in which the next action depends on the past. This "
                        + "comparison does not install label-dependent action choice.")),
                    Paragraph(Text(
                        "Induction on the actual branch evaluation gives the entire "
                        + "substate alpha(w) Uw X Uw*, with alpha(w)=2 to the negative "
                        + "number of J calls. Tree induction gives positive weights with "
                        + "sum one. These weights depend only on the actual tree word, "
                        + "never on X. Trace cyclicity then gives both terminal cells "
                        + "alpha(l) Tr(Rl X) and alpha(l) Tr((I-Rl) X), where "
                        + "Rl=Uw* E Uw. No zero terminal probability is removed or divided "
                        + "by, and both cells together have mass alpha(l).")),
                    Paragraph(Text(
                        "The lifted control is B N B*+(I-BB*). Multiplying the original "
                        + "intertwiners along each actual word gives the same leaf substate "
                        + "on inputs B X B*. Pulling back the lifted terminal by B gives "
                        + "exactly E or I-E. The resulting equality is confined to this "
                        + "code sector; it makes no claim for arbitrary five-dimensional inputs.")),
                    Paragraph(Text(
                        "Stochastic t is one joint kernel c(l,b,a), nonnegative and "
                        + "summing to one over the three a labels at each complete record "
                        + "(l,b). Its effects are the sum over actual leaves of "
                        + "alpha(l)[c(l,1,a)Rl+c(l,0,a)(I-Rl)]. The theorem derives the "
                        + "Born pairing for every mathematical input matrix and proves "
                        + "positive normalized output distributions for every density input. "
                        + "The stochastic kernel and convex hull are mathematical outer "
                        + "comparisons; they grant neither an external coin nor independent "
                        + "choice of simulators or mixing weights.")),
                    Paragraph(Text(
                        "RankOneContext 3 is the existing algebraic carrier for a complete "
                        + "normalized rank-one projective basis. PureStateHandshake supplies "
                        + "the terminal rank-one sandwich. Born positivity bounds every "
                        + "basis overlap between zero and one. Each of the two terminal "
                        + "cells contributes at most one to the sum of the three correct "
                        + "responses, so each actual leaf contributes at most two. The "
                        + "derived weights sum to one, yielding score at most 2/3.")),
                    Paragraph(Text(
                        "BasisObstruction states this score bound, maximum operator "
                        + "distance at least 1/3, and a mathematical basis-state witness. "
                        + "The witness output is a nonnegative three-label distribution "
                        + "of mass one whose total variation from the ideal point mass "
                        + "is at least 1/3. The singleton event gives the TV bound through "
                        + "TotalVariation.Metric.total_variation_eq_sup_event_gap. These "
                        + "basis states are separation witnesses, not installed preparations.")),
                    Paragraph(Text(
                        "The matrix norm is explicitly Mathlib's Hilbert-L2 operator "
                        + "norm: it equals the continuous-linear-map norm of toEuclideanCLM. "
                        + "maxDistance is the maximum of the three individual matrix "
                        + "distances and is proved equal to the finite-product norm. The "
                        + "score is continuous and real linear in this topology. Its "
                        + "2/3 halfspace and the set of POVMs are closed and convex. Their "
                        + "intersection contains the operational image, hence its convex "
                        + "hull and closure. The same score, distance and normalized TV "
                        + "conclusions follow throughout that closure.")),
                    Paragraph(Text(
                        "Three separately approximated binary effects do not define one "
                        + "joint ternary POVM. Probability effects do not determine "
                        + "successor instruments. The result concerns the original single "
                        + "terminal and classical postprocessing, with no reset, copy, "
                        + "inverse gate, extra effect, coherent label access, postselection, "
                        + "unread branch or postterminal quantum continuation."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(params Formula[] clauses) => clauses.Length == 1
        ? clauses[0]
        : new Formula.Logic(clauses[0], FormulaLogicOperator.And, And(clauses[1..]));
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Leq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Times(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula SumOver(Formula v, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(v, Sp, InMacro, Sp, domain), Sp, body);
    private static Formula TrRe(Formula x) => Call("real", Call("Tr", x));
    private static Formula TheoremFormula()
    {
        Formula S = F.Id("S"), Hh = F.Id("H"), t = F.Id("t"), l = F.Id("l");
        Formula X = F.Id("X"), b = F.Id("b"), a = F.Id("a"), c = F.Id("c");
        Formula B = F.Id("B"), M = F.Id("M"), L = F.Id("L"), r = F.Id("r");
        Formula s = F.Id("s"), k = F.Id("k"), h = F.Id("h"), m = F.Id("m");
        Formula v = F.Id("v"), p = F.Id("p");
        Formula zero = D(0), one = D(1);
        Formula twoThirds = new Formula.Fraction(D(2), D(3));
        Formula mat = Call("Mat"), tuple = Call("Tuple"), real = Call("Real");
        Formula bit = Call("Bool"), labels = Call("Fin", D(3));
        Formula leaves = Call("Leaf", t), word = Call("word", t, l);
        Formula weight = Call("alpha", word), U = Call("wordUnitary", S, word);
        Formula R = Call("leafProjection", S, t, l);
        Formula density = And(Call("PosSemidef", X), Eqn(Call("Tr", X), one));
        Formula leafProb = Call("leafProbability", S, t, X, l, b);
        Formula leafLaw = All("t", Call("CausalTree", Hh), And(
            Eqn(SumOver(l, leaves, weight), one),
            All("l", leaves, And(
                new Formula.Relation(zero, FormulaRelationOperator.LessThan, weight),
                Eqn(weight, Call("inverse", new Formula.Power(D(2), Call("jcount", word)))),
                Call("IsNormalizedRankOneProjection", R),
                All("X", mat, And(
                    Eqn(Call("leafRun", S, t, l, X),
                        Call("smul", weight, Times(Times(U, X), Call("star", U)))),
                    All("b", bit, Eqn(leafProb,
                        Times(weight, TrRe(Times(Call("ite", b, R,
                            Call("subtract", one, R)), X))))),
                    All("b", bit, Eqn(Call("liftedProbability", S, t, X, l, b), leafProb)),
                    Implies(density, And(All("b", bit, Leq(zero, leafProb)),
                        Eqn(SumOver(b, bit, leafProb), weight)))))))));
        Formula effect = Call("effects", S, t, c);
        Formula post = Call("postProbability", S, t, c, X, a);
        Formula postLaw = All("t", Call("CausalTree", Hh),
            All("c", Call("Stochastic", t), And(
                Call("IsPOVM", effect),
                All("X", mat, All("a", labels,
                    Eqn(post, TrRe(Times(Call("apply", effect, a), X))))),
                All("X", mat, Implies(density, And(All("a", labels, Leq(zero, post)),
                    Eqn(SumOver(a, labels, post), one)))),
                All("B", Call("RankOneContext", D(3)), Call("BasisObstruction", B, effect)))));
        Formula scoreM = Call("score", B, M);
        Formula halfspace = Seq(OpenBrace, M, Sp, Mid, Sp, Leq(scoreM, twoThirds), CloseBrace);
        Formula hull = Call("convexHull", real, Call("operationalImage", S, Hh));
        Formula hullLaw(Formula set) => All("M", tuple, Implies(
            new Formula.Relation(M, FormulaRelationOperator.MemberOf, set),
            And(Call("IsPOVM", M), Call("BasisObstruction", B, M))));
        Formula closureLaw = All("B", Call("RankOneContext", D(3)), And(
            Call("Continuous", Call("score", B)),
            All("M", tuple, All("L", tuple, All("r", real, All("s", real,
                Eqn(Call("score", B, Add(Call("smul", r, M), Call("smul", s, L))),
                    Add(Times(r, scoreM), Times(s, Call("score", B, L)))))))),
            Call("Convex", real, halfspace), Call("IsClosed", halfspace),
            hullLaw(hull), hullLaw(Call("closure", hull)),
            All("M", tuple, Eqn(Call("maxDistance", B, M),
                new Formula.Norm(Call("subtract", M, Call("projector", B)))))));
        Formula tree = Call("fixedStoppingTree", k, h, m, v, p);
        Formula words = Call("List", Call("Letter"));
        Formula fixedLaw = All("k", new Formula.TypeArrow(Call("Nat"), bit),
            All("h", new Formula.TypeArrow(words, bit),
            All("m", new Formula.TypeArrow(words, Hh),
            All("v", Call("List", Call("Action")), All("p", words,
            All("c", Call("Stochastic", tree), new Formula.Relation(
                Call("effects", S, tree, c), FormulaRelationOperator.MemberOf,
                Call("operationalImage", S, Hh))))))));
        Formula prep = Call("preparation", S);
        return Disp(All("S", Call("Source"), All("H", Call("Type"), And(
            And(Call("PosSemidef", prep), Eqn(Call("Tr", prep), one)),
            leafLaw, postLaw, closureLaw,
            All("X", mat, Eqn(new Formula.Norm(X),
                new Formula.Norm(Call("toEuclideanCLM", X)))), fixedLaw))));
    }
}
