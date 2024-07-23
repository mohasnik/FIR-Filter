FILTER_OUTPUT_FILE = "result_outputs.txt"
CORRECT_OUTPUT_FILE = "outputs.txt"

def checkValues(filter_outs, correct_outputs):
    for i in range(len(filter_outs)):
        if(filter_outs[i] != correct_outputs[i]):
            return "WRONG VALUES"

    return "PASS"

filter_out_file = open(FILTER_OUTPUT_FILE, 'r')
filter_outs = filter_out_file.readlines()
filter_out_file.close()

correct_output_file = open(CORRECT_OUTPUT_FILE, 'r')
correct_outputs = correct_output_file.readlines()
correct_output_file.close()

print(checkValues(filter_outs, correct_outputs))



