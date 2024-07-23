
# FIR Filter Design for FPGA-Based Embedded System

This repository contains the implementation of a Finite Impulse Response (FIR) filter designed for noise cancellation of audio signals. The project is part of an FPGA-based embedded system design course assignment.


## Overview

### FIR Filter Theory

FIR (Finite Impulse Response) filters are a type of digital filter with a finite impulse response. They are preferred over IIR (Infinite Impulse Response) filters due to their guaranteed stability and linear phase properties, which are crucial for audio and communication systems.

The filter is defined by the equation:

$$
H(z) = \sum_{n=0}^{M} h[n] \cdot z^{-n}
$$

where \( M \) is the filter order, and \( h[n] \) are the filter coefficients.

### Filter Structure

The audio signal used in this project is located in `input_files/input.wav`. The converted fixed-point values of this signal are available in `input.txt`. These values are in fixedpoint<16, 15> format, as they range between -1 and 1. Consequently, a lowpass filter with an order of 64 (M = 64) is chosen for this application.

### Implementation Details

#### Datapath Design

The following picture illustrates the architecture of the datapath of the FIR filter:

<p align="center">
  <img src="https://github.com/user-attachments/assets/144c54a5-d145-4099-a02a-9ab89418f683" alt="FIR filter datapath" width="600"/>
  <br/>
  Figure 1 - The datapath Structure of FIR Filter.
</p>
<br/>
<br/>

The datapath handles the core computations of the FIR filter, including shifting input data through a shift register and performing multiply-accumulate operations using the filter coefficients. The coefficients are stored in a Look-Up Table (LUT) in reverse order for efficient processing (See [Tools section](#Tools) - Coef_reverser.py). Moreover, the datapath is pipelined for higher clock frequency.

- **Shift Register:** Handles the storage and shifting of input data samples.
- **Multiplier:** Performs the multiplication of input samples with the filter coefficients.
- **Adder:** Accumulates the results of the multiplications to produce the final output.
- **LUT** Contains the coefficients required for the lowpass filter.
- **Word shift Register** stores the new value along with the 63 most recent inputs for filter computation.

#### Control Unit

The control unit manages the operation of the datapath, including the sequencing of data shifts, multiplications, and accumulations. The following figure shows the Finite-State-Machine diagram of the FIR filter:

<p align="center">
  <img src="https://github.com/user-attachments/assets/c9a35186-1756-4fcb-b8bc-c9a2e28e879d" alt="FIR filter controller" width="600"/>
  <br/>
  Figure 2 - The FSM diagram of FIR Filter.
</p>
<br/>
<br/>


Control states include:
1. **IDLE:** Waits for the input_valid signal.
2. **GET_INPUT:** Loads new input data into the shift register.
3. **CALC:** Performs the multiply-accumulate operations.
4. **WAIT_SUM:** Waits for the completion of the accumulation.
5. **READY:** Signals that the output data is ready using output_valid signal.

### Verilog Modules

- **FIR.sv:** Top-level module that integrates the datapath and control unit.
- **FIR_DP.sv:** Datapath module containing the shift register, multipliers, and adders.
- **FIR_CT.sv:** Control unit module that manages the state transitions and control signals.
- **FIR_TB.sv:** Testbench for verifying the functionality of the FIR filter.
- **counter.v, LUT.v, comparator.v, multiplier.v, adder.v, register_clr.v, register_freeze.v, word_shift_register.v:** Supporting modules for the datapath and control unit.

### Simulation

- **Modelsim:** Used for functional simulation of the FIR filter.
  - The testbench reads input data from `coeffs_reversed.txt`, processes it through the FIR filter, and writes the output to `result_outputs.txt`.
  - The expected output is compared with the results in `outputs.txt` to verify correctness.
  - Using the provided MATLAB scripts, you can convert the signals back to the `.wav` audio format to verify the correctness of the noise cancellation process.

- **Assertions** are used to verify the correctness of the design during simulation:
  1. **done_sig:** Ensures that the control unit correctly transitions to the done state.
  2. **Proper_shift:** Verifies that data shifting within the shift register is accurate.
  3. **Adder_loop:** Checks the correctness of the accumulation in the adder loop.



### Synthesis

To explore the architecture and implementation, the FIR filter is synthesized on a Cyclone II FPGA with different bit widths and filter orders to compare the area used and performance.

<p align="center" > Table 1. Synthesis Report of FIR Filter with different Parameters </p>

| Number of Multiplier Blocks   | Total Number of Memory Bits    | Registers    | Logic Elements   | Number of Coefficients | Bit Width
|-------------|-------------|-------------|-------------|-------------|-------------|
| 1 | 384 | 42 | 111 | 50 | 8 |
| 1 | 784 | 45 | 118 | 100 | 8 |
| 2 | 768 | 58 | 178 | 50 | 16 |
| 2 | 1568 | 61 | 188 | 100 | 16 |




### Tools

- **coefs_reverser.py:** A Python script to reverse the order of filter coefficients for LUT initialization. As explained in the datapath descriptions, to maintain a simplified architecture for the FIR filter, the coefficients of the lowpass filter should be loaded into the LUT in reversed order. This Python script is provided to create the corresponding initial file for the LUT.
- **play_output.m:** A MATLAB script for playing the audio file after filtering.
- **create_output_audio.m:** A MATLAB script to create audio file from FIR filter output file.



### References

1. L. Wanhammer, “DSP Integrated Circuits”, Academic press, New York, 1999.
2. A. V. Oppenheim, R. W. Schafer, and J. R. Buck, “Discrete-Time Signal Processing”, 2nd ed., Upper Saddle River, NJ: Prentice Hall, 1999.
3. Wikipedia, The Free Encyclopedia, “Finite impulse response”.


## License

This project is licensed under the MIT License.
