from flask import Flask, request, jsonify
from parser import parse_program
from ssa import convert_to_ssa, unroll_loops
from smt import check_assertion, check_equivalence
from verifier import verify_program, check_program_equivalence
import traceback
from flask_cors import CORS



app = Flask(__name__)
CORS(app)  # This allows all origins by default (you can restrict it later)


@app.route('/analyze', methods=['POST'])
def analyze():
    try:
        data = request.json
        code = data.get('code', '')
        mode = data.get('mode', 'verification')
        unroll_depth = data.get('unroll_depth', 2)
        other_code = data.get('other_code', '')

        # Parse the main program
        ast1 = parse_program(code)
        ssa1 = convert_to_ssa(ast1)
        unrolled_ssa1 = unroll_loops(ssa1, unroll_depth)

        result = {
            'ast': str(ast1),
            'ssa': ssa1.to_string(),
            'unrolled_ssa': unrolled_ssa1.to_string(),
            'verification_result': None,
            'equivalence_result': None,
            'smt_code': None,
            'error': None
        }

        if mode == 'verification':
            # Generate SMT for verification
            smt_code = generate_smt(unrolled_ssa1)
            verification_result = verify_program(unrolled_ssa1)
            
            result.update({
                'smt_code': smt_code,
                'verification_result': {
                    'all_assertions_hold': verification_result[0],
                    'examples': verification_result[1],
                    'counterexamples': verification_result[2]
                }
            })

        elif mode == 'equivalence':
            # Parse the second program
            ast2 = parse_program(other_code)
            ssa2 = convert_to_ssa(ast2)
            unrolled_ssa2 = unroll_loops(ssa2, unroll_depth)

            # Generate SMT for equivalence
            smt_code = generate_smt(unrolled_ssa1, unrolled_ssa2)
            equivalence_result = check_program_equivalence(unrolled_ssa1, unrolled_ssa2)
            
            result.update({
                'other_ast': str(ast2),
                'other_ssa': ssa2.to_string(),
                'other_unrolled_ssa': unrolled_ssa2.to_string(),
                'smt_code': smt_code,
                'equivalence_result': {
                    'equivalent': equivalence_result[0],
                    'examples': equivalence_result[1],
                    'counterexamples': equivalence_result[2]
                }
            })

        return jsonify(result)

    except Exception as e:
        return jsonify({
            'error': str(e),
            'traceback': traceback.format_exc()
        }), 400

def generate_smt(ssa1, ssa2=None):
    """Generate SMT code for verification or equivalence checking."""
    from smt import generate_smt as smt_generator
    if ssa2 is None:
        return smt_generator(ssa1)
    else:
        return smt_generator(ssa1, ssa2)

if __name__ == '__main__':
    app.run(debug=True)