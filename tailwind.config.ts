import type { Config } from 'tailwindcss';

export default {
  content: ['./src/**/*.{ts,tsx}'],
  darkMode: 'class',
  theme: {
    extend: {
      colors: {
        brand: {
          50: '#eef6ff',
          100: '#d9eaff',
          200: '#bcdaff',
          300: '#8ec2ff',
          400: '#599fff',
          500: '#3479fc',
          600: '#1e5af1',
          700: '#1745de',
          800: '#1a39b4',
          900: '#1b358e',
        },
      },
      fontFamily: {
        mono: ['"JetBrains Mono"', '"DejaVu Sans Mono"', 'Menlo', 'Consolas', 'monospace'],
      },
    },
  },
  plugins: [],
} satisfies Config;
