using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;
internal sealed class QubitEntropyContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic contraction for an actual symmetric qubit ensemble", H("QubitEntropyContraction"), Blocks(
            Describe.Lean(DescribeId.Create("holevo-contraction"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction"),
                H("Quadratic contraction for an actual symmetric qubit ensemble"), StatementSource.FromAuthor(Seq(Forall, Sp, Seq(F.Id("x"), Comma, F.Id("z"), Comma, F.Id("t")), Colon, Seq(Mathbb, Grp(F.Id("R"))), Comma, Esc, Seq(Grp(Seq(Seq(Seq(Seq(Open, Seq(F.Id("x"), Caret, Grp(D(2))), Close), Plus, Seq(Open, Seq(F.Id("z"), Caret, Grp(D(2))), Close)), Le, Sp, D(1)), Land, Sp, Seq(D(0), Le, Sp, F.Id("t")), Land, Sp, Seq(F.Id("t"), Le, Sp, D(1)))), Implies, Sp, Seq(Seq(D(0), Le, Sp, Call("qubitHolevo", F.Id("x"), Seq(Seq(Open, F.Id("t"), Close), Times, Sp, Seq(Open, F.Id("z"), Close)))), Land, Sp, Seq(Call("qubitHolevo", F.Id("x"), Seq(Seq(Open, F.Id("t"), Close), Times, Sp, Seq(Open, F.Id("z"), Close))), Le, Sp, Seq(Seq(Open, Seq(F.Id("t"), Caret, Grp(D(2))), Close), Times, Sp, Seq(Open, Call("qubitHolevo", F.Id("x"), F.Id("z")), Close))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/codex2026productmargin")),
                Blocks(
                    Paragraph(Text("For every point of the closed qubit disk and every t in [0,1], the symmetric binary Holevo entropy is nonnegative and contracts by at most t squared when z is replaced by tz. The proof derives concavity of u mapped to binary entropy of (1+sqrt(u))/2 from scalar derivatives on (0,1), with continuity at both endpoints. The matrix statement then uses the actual qubit density states and their spectral entropy, including pure, zero-separation and maximal-mixing cases.")),
                    Paragraph(Text("An application to three real coordinates uses binary entropy in nats. For p in the closed unit interval, write "),
                        Math(Seq(Call("h", F.Id("p")), Eq, Minus, F.Id("p"), Thin, Call("ln", F.Id("p")), Minus, Open, D(1), Minus, F.Id("p"), Close, Thin, Call("ln", Seq(D(1), Minus, F.Id("p"))))),
                        Text(". Each zero-times-log-zero endpoint term is defined as zero, and all logarithms are natural.")),
                    Paragraph(Text("For any real r in [-1,1], specialize qubit_holevo_contraction with its parameters x=0, z=1 and t=abs(r). The disk hypothesis holds at (0,1), and abs(r) lies in [0,1]. Unfolding QubitNormalFormState.qubitHolevo and QubitNormalFormState.qubit_state_entropy identifies the scaled Holevo entropy with ln(2) minus h((1+abs(r))/2), while the unscaled value is ln(2). The identity sqrt(r squared)=abs(r) and binary-entropy symmetry h(p)=h(1-p) remove the absolute value; h(1/2)=ln(2) and h(1)=0 evaluate the endpoints. The contraction therefore gives "),
                        Math(Seq(Call("ln", D(2)), Minus, Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("r")), Grp(D(2)))), Le, Sp, F.Id("r"), Caret, Grp(D(2)), Thin, Call("ln", D(2)))),
                        Text(". This includes both signs and the endpoint coordinates.")),
                    Paragraph(Text("Now let x, y and z be real numbers in the closed unit ball, so their squared coordinates sum to at most one. Each coordinate is in [-1,1]. Applying the preceding bound to each coordinate and adding yields "),
                        Math(Seq(Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("x")), Grp(D(2)))), Plus,
                            Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("y")), Grp(D(2)))), Plus,
                            Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("z")), Grp(D(2)))),
                            Ge, Sp, Open, D(3), Minus, Open, F.Id("x"), Caret, Grp(D(2)), Plus, F.Id("y"), Caret, Grp(D(2)), Plus, F.Id("z"), Caret, Grp(D(2)), Close, Close, Thin, Call("ln", D(2)),
                            Ge, Sp, D(2), Thin, Call("ln", D(2)))),
                        Text(". The last step uses nonnegativity of ln(2), so the conclusion covers the entire closed ball, including its interior and boundary.")),
                    Paragraph(Text("At (1,0,0) the three entropy values are 0, ln(2) and ln(2). Changing the nonzero coordinate to -1 or permuting coordinates gives the same total. Thus the universal lower bound 2 ln(2) is sharp.")),
                    Paragraph(Text("The equality cases follow from the existing private radial_concave lemma in QubitEntropyContraction. Set L=ln(2)>0 and f(u)=h((1+sqrt(u))/2) for u in [0,1]. This lemma supplies concavity of f, with f(0)=L and f(1)=0. Subtract the endpoint chord to define g(u)=f(u)-(1-u)L. Then g is concave, g(0)=g(1)=0, and g(u) is nonnegative throughout [0,1]. At the interior point u=1/4, sqrt(u)=1/2 and h(3/4)=2L-(3/4)ln(3), so "),
                        Math(Seq(Call("g", Seq(Frac, Grp(D(1)), Grp(D(4)))), Eq,
                            Frac, Grp(D(5), F.Id("L"), Minus, D(3), Call("ln", D(3))), Grp(D(4)), Eq,
                            Frac, Grp(Call("ln", D(32)), Minus, Call("ln", D(27))), Grp(D(4)), Gt, Sp, D(0))),
                        Text(". The logarithm identities ln(32)=5 ln(2) and ln(27)=3 ln(3), together with 0<27<32 and strict increase of the natural logarithm on positive numbers, give this strict sign.")),
                    Paragraph(Text("For 0<u<=1/4, write u=(1-4u)0+(4u)(1/4). Both weights are nonnegative and sum to one. Concavity of g gives "),
                        Math(Seq(Call("g", F.Id("u")), Ge, Sp, D(4), F.Id("u"), Thin,
                            Call("g", Seq(Frac, Grp(D(1)), Grp(D(4)))), Gt, Sp, D(0))),
                        Text(". For 1/4<u<1, write u=(4(1-u)/3)(1/4)+((4u-1)/3)1. Again the weights are nonnegative and sum to one, and concavity gives "),
                        Math(Seq(Call("g", F.Id("u")), Ge, Sp, Frac, Grp(D(4), Open, D(1), Minus, F.Id("u"), Close), Grp(D(3)), Thin,
                            Call("g", Seq(Frac, Grp(D(1)), Grp(D(4)))), Gt, Sp, D(0))),
                        Text(". Hence g(u)>0 for every 0<u<1. This uses the existing concavity and one positive chord gap; no strict-concavity assertion or new derivative argument is needed.")),
                    Paragraph(Text("For any real r in [-1,1], sqrt(r squared)=abs(r), and entropy symmetry identifies f(r squared) with h((1+r)/2) for both signs of r. Consequently the coordinate gap "),
                        Math(Seq(Call("h", Seq(Frac, Grp(D(1), Plus, F.Id("r")), Grp(D(2)))), Minus,
                            Open, D(1), Minus, F.Id("r"), Caret, Grp(D(2)), Close, F.Id("L"), Eq,
                            Call("g", Seq(F.Id("r"), Caret, Grp(D(2)))))),
                        Text(" is nonnegative, is strictly positive when 0<r squared<1, and vanishes exactly when r squared is 0 or 1. The endpoint evaluations include r=0 and r=+1 or -1.")),
                    Paragraph(Text("Write H=h((1+x)/2)+h((1+y)/2)+h((1+z)/2) and s=x squared+y squared+z squared. The preceding identities give the exact slack decomposition "),
                        Math(Seq(F.Id("H"), Minus, D(2), F.Id("L"), Eq,
                            Open, D(1), Minus, F.Id("s"), Close, F.Id("L"), Plus,
                            Call("g", Seq(F.Id("x"), Caret, Grp(D(2)))), Plus,
                            Call("g", Seq(F.Id("y"), Caret, Grp(D(2)))), Plus,
                            Call("g", Seq(F.Id("z"), Caret, Grp(D(2)))))),
                        Text(". Under the closed-ball hypothesis s<=1, all four terms on the right are nonnegative. Thus H=2L forces s=1, since L>0, and each coordinate gap must vanish. Each squared coordinate is therefore 0 or 1; their sum being one forces exactly one to be one and the other two to be zero. Conversely, each such triple has entropy values 0,L,L in some order, so H=2L.")),
                    Paragraph(Text("For every real x,y,z with x squared+y squared+z squared<=1, the complete conclusion is H>=2 ln(2), with H=2 ln(2) if and only if (x squared=1 and y=z=0), or (y squared=1 and x=z=0), or (z squared=1 and x=y=0). Equivalently, the minimizers are exactly (1,0,0), (-1,0,0), (0,1,0), (0,-1,0), (0,0,1) and (0,0,-1). Every interior point has H>2 ln(2). This is a reuse consequence of the existing scalar concavity and contraction, not an additional mathematical declaration. The argument concerns real coordinates and natural-logarithm binary entropy; it supplies no physical Born-probability mapping or stronger uncertainty relation, and makes no literature novelty claim or attribution of the equality classification to a primary paper."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
